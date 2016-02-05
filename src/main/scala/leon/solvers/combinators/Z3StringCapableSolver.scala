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
  def convert(p: Program, force: Boolean = false): (Program, Option[Z3StringConversion]) = {
    val converter = new Z3StringConversion(p)
    import converter.Forward._
    var globalFdMap = Map[FunDef, (Map[Identifier, Identifier], FunDef)]()
    var hasStrings = false
    val program_with_strings = converter.getProgram
    val (new_program, fdMap) = DefOps.replaceFunDefs(program_with_strings)((fd: FunDef) => {
      globalFdMap.get(fd).map(_._2).orElse(
          if( fd.body.map(exists(e => TypeOps.exists{ _== StringType }(e.getType))).getOrElse(false) ||
              fd.paramIds.exists(id => TypeOps.exists(_ == StringType)(id.getType))) {
            val idMap = fd.params.map(vd => vd.id -> convertId(vd.id)).toMap
            val newFdId = convertId(fd.id)
            val newFd = fd.duplicate(newFdId,
                fd.tparams,
                fd.params.map(vd => ValDef(idMap(vd.id))),
                convertType(fd.returnType))
            globalFdMap += fd -> ((idMap, newFd))
            hasStrings = hasStrings || (program_with_strings.library.escape.get != fd)
            Some(newFd)
          } else None
      )
    })
    if(!hasStrings && !force) {
      (p, None)
    } else {
      converter.globalFdMap ++= globalFdMap.view.map(kv => (kv._1, kv._2._2))
      for((fd, (idMap, newFd)) <- globalFdMap) {
        implicit val idVarMap = idMap.mapValues(id => Variable(id))
        newFd.fullBody = convertExpr(newFd.fullBody)
      }
      (new_program, Some(converter))
    }
  }
}
trait ForcedProgramConversion { self: Z3StringCapableSolver[_] =>
  override def convertProgram(p: Program): (Program, Option[Z3StringConversion]) = {
    Z3StringCapableSolver.convert(p, true)
  }
}

abstract class Z3StringCapableSolver[+TUnderlying <: Solver](val context: LeonContext, val program: Program,
    val underlyingConstructor: (Program, Option[Z3StringConversion]) => TUnderlying)
extends Solver {
  def convertProgram(p: Program): (Program, Option[Z3StringConversion]) = Z3StringCapableSolver.convert(p)
  protected val (new_program, someConverter) = convertProgram(program)

  val underlying = underlyingConstructor(new_program, someConverter)
  
  def getModel: leon.solvers.Model = {
    val model = underlying.getModel
    someConverter match {
      case None => model
      case Some(converter) =>
        println("Conversion")
        val ids = model.ids.toSeq
        val exprs = ids.map(model.apply)
        import converter.Backward._
        val original_ids = ids.map(convertId)
        val original_exprs = exprs.map{ case e => convertExpr(e)(Map()) }
        new Model(original_ids.zip(original_exprs).toMap)
    }
  }
  
  // Members declared in leon.utils.Interruptible
  def interrupt(): Unit = underlying.interrupt()
  def recoverInterrupt(): Unit = underlying.recoverInterrupt()

  // Members declared in leon.solvers.Solver
  def assertCnstr(expression: Expr): Unit = {
    someConverter.map{converter => 
      import converter.Forward._
      val newExpression = convertExpr(expression)(Map())
      underlying.assertCnstr(newExpression)
    }.getOrElse(underlying.assertCnstr(expression))
  }
  def getUnsatCore: Set[Expr] = {
    someConverter.map{converter => 
      import converter.Backward._
      underlying.getUnsatCore map (e => convertExpr(e)(Map()))
    }.getOrElse(underlying.getUnsatCore)
  }
  def check: Option[Boolean] = underlying.check
  def free(): Unit = underlying.free()
  def pop(): Unit = underlying.pop()
  def push(): Unit = underlying.push()
  def reset(): Unit = underlying.reset()
  def name: String = underlying.name
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
  override def getModel = {
    val model = underlying.getModel
    someConverter map { converter =>
      val ids = model.ids.toSeq
      val exprs = ids.map(model.apply)
      import converter.Backward._
      val original_ids = ids.map(convertId)
      val original_exprs = exprs.map{ case e => convertExpr(e)(Map()) }

      model match {
        case hm: HenkinModel =>
          val new_domain = new HenkinDomains(
              hm.doms.lambdas.map(kv =>
                (convertExpr(kv._1)(Map()).asInstanceOf[Lambda],
                 kv._2.map(e => e.map(e => convertExpr(e)(Map()))))).toMap,
              hm.doms.tpes.map(kv =>
                (convertType(kv._1),
                 kv._2.map(e => e.map(e => convertExpr(e)(Map()))))).toMap
              )
      
          new HenkinModel(original_ids.zip(original_exprs).toMap, new_domain)
        case _ => model
      }
    } getOrElse model
  }
}

class ConvertibleCodeGenEvaluator(context: LeonContext, originalProgram: Program, val converter: Z3StringConversion)
    extends CodeGenEvaluator(context, originalProgram) {

  override def compile(expression: Expr, args: Seq[Identifier]) : Option[solvers.Model=>EvaluationResult] = {
    import converter._ 
    super.compile(Backward.convertExpr(expression)(Map()), args.map(Backward.convertId))
      .map(evaluator => (m: Model) => Forward.convertResult(evaluator(Backward.convertModel(m)))
    )
  }
}

class ConvertibleDefaultEvaluator(context: LeonContext, originalProgram: Program, val converter: Z3StringConversion)
    extends DefaultEvaluator(context, originalProgram) {

  override def eval(ex: Expr, model: Model): EvaluationResults.Result[Expr] = {
    import converter._
    Forward.convertResult(super.eval(Backward.convertExpr(ex)(Map()), Backward.convertModel(model)))
  }
}


class FairZ3SolverWithBackwardEvaluator(context: LeonContext, program: Program,
    originalProgram: Program, someConverter: Option[Z3StringConversion]) extends FairZ3Solver(context, program) {
  override lazy val evaluator: DeterministicEvaluator = { // We evaluate expressions using the original evaluator
    someConverter match {
      case Some(converter) =>
        if (useCodeGen) {
          new ConvertibleCodeGenEvaluator(context, originalProgram, converter)
        } else {
          new ConvertibleDefaultEvaluator(context, originalProgram, converter)
        }
      case None =>
        if (useCodeGen) {
          new CodeGenEvaluator(context, program)
        } else {
          new DefaultEvaluator(context, program)
        }
    }
  }
}


class Z3StringFairZ3Solver(context: LeonContext, program: Program)
  extends Z3StringCapableSolver(context, program,
      (prgm: Program, someConverter: Option[Z3StringConversion]) =>
        new FairZ3SolverWithBackwardEvaluator(context, prgm, program, someConverter)) 
  with Z3StringEvaluatingSolver[FairZ3Solver]
  with Z3StringQuantificationSolver[FairZ3Solver] {
     // Members declared in leon.solvers.z3.AbstractZ3Solver
    protected[leon] val z3cfg: _root_.z3.scala.Z3Config = underlying.z3cfg
    override def checkAssumptions(assumptions: Set[Expr]): Option[Boolean] = {
      someConverter match {
        case None => underlying.checkAssumptions(assumptions)
        case Some(converter) =>
          underlying.checkAssumptions(assumptions map (e => converter.Forward.convertExpr(e)(Map())))
      }
    }
}

class Z3StringUnrollingSolver(context: LeonContext, program: Program, underlyingSolverConstructor: Program => Solver)
  extends Z3StringCapableSolver(context, program, (program: Program, converter: Option[Z3StringConversion]) =>
    new UnrollingSolver(context, program, underlyingSolverConstructor(program)))
  with Z3StringNaiveAssumptionSolver[UnrollingSolver]
  with Z3StringEvaluatingSolver[UnrollingSolver]
  with Z3StringQuantificationSolver[UnrollingSolver] {
    override def getUnsatCore = super[Z3StringNaiveAssumptionSolver].getUnsatCore
}

class Z3StringSMTLIBZ3QuantifiedSolver(context: LeonContext, program: Program)
  extends Z3StringCapableSolver(context, program, (program: Program, converter: Option[Z3StringConversion]) =>
    new smtlib.SMTLIBZ3QuantifiedSolver(context, program)) {
     override def checkAssumptions(assumptions: Set[Expr]): Option[Boolean] = {
      someConverter match {
        case None => underlying.checkAssumptions(assumptions)
        case Some(converter) =>
          underlying.checkAssumptions(assumptions map (e => converter.Forward.convertExpr(e)(Map())))
      }
    }
}

