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
import leon.solvers.z3.Z3StringConversionReverse

object Z3StringCapableSolver {
  def convert(p: Program): ((Program, Map[FunDef, FunDef]), Z3StringConversionReverse, Map[Identifier, Identifier]) = {
    val converter = new Z3StringConversionReverse {
      def getProgram = p
      
      def convertId(id: Identifier): (Identifier, Variable) = {
        id -> Variable(FreshIdentifier(id.name, convertType(id.getType)))
      }
      def convertToTarget(e: Expr)(implicit bindings: Map[Identifier, Expr]): Expr = e match {
        case Variable(id) if bindings contains id => bindings(id)
        case Let(a, expr, body) if TypeOps.exists( _ == StringType)(a.getType) => 
          val new_a_bid = convertId(a)
          val new_bindings = bindings + new_a_bid
          val expr2 = convertToTarget(expr)(new_bindings)
          val body2 = convertToTarget(expr)(new_bindings)
          Let(new_a_bid._1, expr2, body2)
        case StringConverted(p) => p
        case Operator(es, builder) =>
          val rec = convertToTarget _
          val newEs = es.map(rec)
          if ((newEs zip es).exists { case (bef, aft) => aft ne bef }) {
            builder(newEs).copiedFrom(e)
          } else {
            e
          }
      }
      def targetApplication(fd: TypedFunDef, args: Seq[Expr])(implicit bindings: Map[Identifier, Expr]): Expr = {
        FunctionInvocation(fd, args)
      }
    }
    import converter._
    var globalIdMap = Map[Identifier, Identifier]()
    (DefOps.replaceFunDefs(p)((fd: FunDef) => {
      if( fd.body.map(exists(e => TypeOps.exists{ _== StringType }(e.getType))).getOrElse(false) ||
          fd.paramIds.exists(id => TypeOps.exists(_ == StringType)(id.getType))) {
        
        val idMap = fd.params.map(vd => vd.id -> FreshIdentifier(vd.id.name, convertType(vd.id.getType))).toMap
        globalIdMap ++= idMap
        implicit val idVarMap = idMap.mapValues(id => Variable(id))
        
        val newFd = fd.duplicate(FreshIdentifier(fd.id.name, convertType(fd.id.getType)),
            fd.tparams,
            fd.params.map(vd => ValDef(idMap(vd.id))),
            convertType(fd.returnType))
        fd.body foreach { body =>
          newFd.body = Some(convertToTarget(body))
        }
        Some(newFd)
      } else None
    }), converter, globalIdMap)
  }
}

class Z3StringCapableSolver(val context: LeonContext, val program: Program, f: Program => UnrollingSolver)  extends Solver
     with NaiveAssumptionSolver
     with EvaluatingSolver
     with QuantificationSolver  {
  
  val ((new_program, mappings), converter, idMap) = Z3StringCapableSolver.convert(program)

  val idMapReverse = idMap.map(kv => kv._2 -> kv._1).toMap
  val underlying = f(new_program)

  // Members declared in leon.solvers.EvaluatingSolver
  val useCodeGen: Boolean = underlying.useCodeGen

  // Members declared in leon.utils.Interruptible
  def interrupt(): Unit = underlying.interrupt()
  def recoverInterrupt(): Unit = underlying.recoverInterrupt()

  // Members declared in leon.solvers.QuantificationSolver
  def getModel: leon.solvers.HenkinModel = {
    val model = underlying.getModel
    val ids = model.ids.toSet
    val exprs = ids.map(model.apply)
    val original_ids = ids.map(idMapReverse) // Should exist.
    val original_exprs = exprs.map(e => converter.StringConversion.reverse(e))
    new HenkinModel(original_ids.zip(original_exprs).toMap, model.doms) // TODO: Convert the domains as well
  }

  // Members declared in leon.solvers.Solver
  def assertCnstr(expression: leon.purescala.Expressions.Expr): Unit = {
    underlying.assertCnstr(converter.convertToTarget(expression)(Map()))
  }
  def check: Option[Boolean] = underlying.check
  def free(): Unit = underlying.free()
  def name: String = "String" + underlying.name
  def pop(): Unit = underlying.pop()
  def push(): Unit = underlying.push()
  def reset(): Unit = underlying.reset()
}