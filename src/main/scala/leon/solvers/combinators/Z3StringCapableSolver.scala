/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package combinators

import purescala.Common._
import purescala.Definitions._
import purescala.Quantification._
import purescala.Constructors._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import purescala.DefOps
import purescala.TypeOps
import purescala.Extractors._
import utils._
import z3.FairZ3Component.{optFeelingLucky, optUseCodeGen, optAssumePre, optNoChecks, optUnfoldFactor}
import templates._
import evaluators._
import Template._
import leon.solvers.z3.Z3StringConversion
import leon.utils.Bijection
import leon.solvers.z3.StringEcoSystem

object Z3StringCapableSolver {
  def convert(p: Program): ((Program, Map[FunDef, FunDef]), Z3StringConversion, Map[Identifier, Identifier]) = {
    val converter = new Z3StringConversion(p)
    import converter._
    import converter.Forward._
    var globalIdMap = Map[Identifier, Identifier]()
    var globalFdMap = Map[FunDef, (Map[Identifier, Identifier], FunDef)]()
    val (new_program, fdMap) = DefOps.replaceFunDefs(converter.getProgram)((fd: FunDef) => {
      globalFdMap.get(fd).map(_._2).orElse(
          if( fd.body.map(exists(e => TypeOps.exists{ _== StringType }(e.getType))).getOrElse(false) ||
              fd.paramIds.exists(id => TypeOps.exists(_ == StringType)(id.getType))) {
            val idMap = fd.params.map(vd => vd.id -> convertId(vd.id)).toMap
            globalIdMap ++= idMap
            val newFdId = convertId(fd.id)
            val newFd = fd.duplicate(newFdId,
                fd.tparams,
                fd.params.map(vd => ValDef(idMap(vd.id))),
                convertType(fd.returnType))
            globalFdMap += fd -> ((idMap, newFd))
            Some(newFd)
          } else None
      )
    })
    converter.globalFdMap ++= globalFdMap.view.map(kv => (kv._1, kv._2._2))
    for((fd, (idMap, newFd)) <- globalFdMap) {
      implicit val idVarMap = idMap.mapValues(id => Variable(id))
      newFd.fullBody = convertExpr(newFd.fullBody)
    }
    ((new_program, fdMap), converter, globalIdMap)
  }
}

abstract class Z3StringCapableSolver[+TUnderlying <: Solver](val context: LeonContext, val program: Program, val underlyingConstructor: Program => TUnderlying)
extends Solver {
  protected val ((new_program, mappings), converter, idMap) = Z3StringCapableSolver.convert(program)

  val idMapReverse = idMap.map(kv => kv._2 -> kv._1).toMap
  val underlying = underlyingConstructor(new_program)
  
  def getModel: leon.solvers.Model = underlying.getModel
  
  // Members declared in leon.utils.Interruptible
  def interrupt(): Unit = underlying.interrupt()
  def recoverInterrupt(): Unit = underlying.recoverInterrupt()

  // Members declared in leon.solvers.Solver
  def assertCnstr(expression: leon.purescala.Expressions.Expr): Unit = {
    val expression2 = DefOps.replaceFunCalls(expression, mappings.withDefault { x => x }.apply _)
    import converter.Forward._
    val newExpression = convertExpr(expression2)(idMap.mapValues(Variable))
    underlying.assertCnstr(newExpression)
  }
  def getUnsatCore: Set[Expr] = {
    import converter.Backward._
    underlying.getUnsatCore map (e => convertExpr(e)(Map()))
  }
  def check: Option[Boolean] = underlying.check
  def free(): Unit = underlying.free()
  def pop(): Unit = underlying.pop()
  def push(): Unit = underlying.push()
  def reset(): Unit = underlying.reset()
}

import z3._

trait Z3StringAbstractZ3Solver[TUnderlying <: Solver] extends AbstractZ3Solver { self: Z3StringCapableSolver[TUnderlying] =>
}

trait Z3StringNaiveAssumptionSolver[TUnderlying <: Solver] extends NaiveAssumptionSolver { self:  Z3StringCapableSolver[TUnderlying] =>
}

trait Z3StringEvaluatingSolver[TUnderlying <: EvaluatingSolver] extends EvaluatingSolver{ self:  Z3StringCapableSolver[TUnderlying] =>
  // Members declared in leon.solvers.EvaluatingSolver
  val useCodeGen: Boolean = underlying.useCodeGen
}

trait Z3StringQuantificationSolver[TUnderlying <: QuantificationSolver] extends QuantificationSolver { self:  Z3StringCapableSolver[TUnderlying] =>
  // Members declared in leon.solvers.QuantificationSolver
  override def getModel: leon.solvers.HenkinModel = {
    val model = underlying.getModel
    val ids = model.ids.toSeq
    val exprs = ids.map(model.apply)
    val original_ids = ids.map(idMapReverse) // Should exist.
    import converter.Backward._
    val original_exprs = exprs.zip(original_ids).map{ case (e, id) => convertExpr(e)(Map()) }
    
    val new_domain = new HenkinDomains(
        model.doms.lambdas.map(kv =>
          (convertExpr(kv._1)(Map()).asInstanceOf[Lambda],
           kv._2.map(e => e.map(e => convertExpr(e)(Map()))))).toMap,
        model.doms.tpes.map(kv =>
          (convertType(kv._1),
           kv._2.map(e => e.map(e => convertExpr(e)(Map()))))).toMap
        )
    
    new HenkinModel(original_ids.zip(original_exprs).toMap, new_domain)
  }
}

class Z3StringFairZ3Solver(context: LeonContext, program: Program)
  extends Z3StringCapableSolver(context, program, (program: Program) => new z3.FairZ3Solver(context, program)) 
  with Z3StringAbstractZ3Solver[FairZ3Solver]
  with Z3ModelReconstruction
  with FairZ3Component
  with Z3StringEvaluatingSolver[FairZ3Solver]
  with Z3StringQuantificationSolver[FairZ3Solver] {
     // Members declared in leon.solvers.z3.AbstractZ3Solver
    protected[leon] val z3cfg: _root_.z3.scala.Z3Config = underlying.z3cfg
    override def reset() = super[Z3StringAbstractZ3Solver].reset()
    override def checkAssumptions(assumptions: Set[Expr]): Option[Boolean] = {
      underlying.checkAssumptions(assumptions map (e => converter.Forward.convertExpr(e)(Map())))
    }
}

class Z3StringUnrollingSolver(context: LeonContext, program: Program, underlyingSolverConstructor: Program => Solver)
  extends Z3StringCapableSolver(context, program, (program: Program) => new UnrollingSolver(context, program, underlyingSolverConstructor(program)))
  with Z3StringNaiveAssumptionSolver[UnrollingSolver]
  with Z3StringEvaluatingSolver[UnrollingSolver]
  with Z3StringQuantificationSolver[UnrollingSolver] {
    def name = underlying.name
    override def getUnsatCore = super[Z3StringNaiveAssumptionSolver].getUnsatCore
}

class Z3StringSMTLIBZ3QuantifiedSolver(context: LeonContext, program: Program)
  extends Z3StringCapableSolver(context, program, (program: Program) => new smtlib.SMTLIBZ3QuantifiedSolver(context, program)) {
     def name: String = underlying.name
     def checkAssumptions(assumptions: Set[Expr]): Option[Boolean] = {
      underlying.checkAssumptions(assumptions map (e => converter.Forward.convertExpr(e)(Map())))
    }
}

