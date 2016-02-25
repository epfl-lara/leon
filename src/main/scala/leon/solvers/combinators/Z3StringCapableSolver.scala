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
import templates._
import evaluators._
import Template._
import leon.solvers.z3.Z3StringConversion
import leon.utils.Bijection
import leon.solvers.z3.StringEcoSystem

object Z3StringCapableSolver {
  def thatShouldBeConverted(t: TypeTree): Boolean = TypeOps.exists{ _== StringType }(t)
  def thatShouldBeConverted(e: Expr): Boolean = exists(e => thatShouldBeConverted(e.getType))(e)
  def thatShouldBeConverted(id: Identifier): Boolean = thatShouldBeConverted(id.getType)
  def thatShouldBeConverted(vd: ValDef): Boolean = thatShouldBeConverted(vd.id)
  def thatShouldBeConverted(fd: FunDef): Boolean = {
    (fd.body exists thatShouldBeConverted)|| (fd.paramIds exists thatShouldBeConverted)
  }
  def thatShouldBeConverted(cd: ClassDef): Boolean = cd match {
    case ccd:CaseClassDef =>  ccd.fields.exists(thatShouldBeConverted)
    case _ => false
  }
  def thatShouldBeConverted(p: Program): Boolean = {
    (p.definedFunctions exists thatShouldBeConverted) ||
    (p.definedClasses exists thatShouldBeConverted)
  }
  
  def convert(p: Program): (Program, Option[Z3StringConversion]) = {
    val converter = new Z3StringConversion(p)
    import converter.Forward._
    var hasStrings = false
    val program_with_strings = converter.getProgram
    val (program_with_correct_classes, cdMap, idMap, fdMap) = if(program_with_strings.definedClasses.exists{ case c: CaseClassDef => c.fieldsIds.exists(id => TypeOps.exists{ _ == StringType}(id.getType)) case _ => false}) {
      val res:(Program, Map[ClassDef, ClassDef], Map[Identifier, Identifier], Map[FunDef, FunDef]) = DefOps.replaceCaseClassDefs(program_with_strings)((cd: ClassDef) => {
        cd match {
          case acd:AbstractClassDef => None
          case ccd:CaseClassDef =>
            if(ccd.fieldsIds.exists(id => TypeOps.exists(StringType == _)(id.getType))) {
              Some((parent: Option[AbstractClassType]) => ccd.duplicate(convertId(ccd.id), ccd.tparams, ccd.fieldsIds.map(id => ValDef(convertId(id))), parent, ccd.isCaseObject))
            } else None
        }
      })
      converter.mappedVariables.clear() // We will compose them later, they have been stored in idMap
      res
    } else {
      (program_with_strings, Map[ClassDef, ClassDef](), Map[Identifier, Identifier](), Map[FunDef, FunDef]())
    }
    val fdMapInverse = fdMap.map(kv => kv._2 -> kv._1).toMap
    val idMapInverse = idMap.map(kv => kv._2 -> kv._1).toMap
    var globalFdMap = Map[FunDef, (Map[Identifier, Identifier], FunDef)]()
    val (new_program, _) = DefOps.replaceFunDefs(program_with_correct_classes)((fd: FunDef) => {
      globalFdMap.get(fd).map(_._2).orElse(
          if(thatShouldBeConverted(fd)) {
            val idMap = fd.params.zip(fd.params).map(origvd_vd => origvd_vd._1.id -> convertId(origvd_vd._2.id)).toMap
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
    if(!hasStrings) {
      (p, None)
    } else {
      converter.globalFdMap ++= globalFdMap.view.map(kv => (kv._1, kv._2._2))
      for((fd, (idMap, newFd)) <- globalFdMap) {
        implicit val idVarMap = idMap.mapValues(id => Variable(id))
        newFd.fullBody = convertExpr(newFd.fullBody)
      }
      converter.mappedVariables.composeA(id => idMapInverse.getOrElse(id, id))
      converter.globalFdMap.composeA(fd => fdMapInverse.getOrElse(fd, fd))
      converter.globalClassMap ++= cdMap
      (new_program, Some(converter))
    }
  }
}

abstract class Z3StringCapableSolver[+TUnderlying <: Solver](
  val context: LeonContext,
  val program: Program,
  val underlyingConstructor: (Program, Option[Z3StringConversion]) => TUnderlying) extends Solver {

  protected val (new_program, optConverter) = Z3StringCapableSolver.convert(program)
  var someConverter = optConverter

  val underlying = underlyingConstructor(new_program, someConverter)
  var solverInvokedWithStrings = false
  
  def getModel: leon.solvers.Model = {
    val model = underlying.getModel
    someConverter match {
      case None => model
      case Some(converter) =>
        val ids = model.ids.toSeq
        val exprs = ids.map(model.apply)
        import converter.Backward._
        val original_ids = ids.map(convertId)
        val original_exprs = exprs.map{ case e => convertExpr(e)(Map()) }

        model match {
          case hm: PartialModel =>
            val new_domain = new Domains(
                hm.domains.lambdas.map(kv =>
                  (convertExpr(kv._1)(Map()).asInstanceOf[Lambda],
                   kv._2.map(e => e.map(e => convertExpr(e)(Map()))))).toMap,
                hm.domains.tpes.map(kv =>
                  (convertType(kv._1),
                   kv._2.map(e => e.map(e => convertExpr(e)(Map()))))).toMap
                )
        
            new PartialModel(original_ids.zip(original_exprs).toMap, new_domain)
          case _ =>
        new Model(original_ids.zip(original_exprs).toMap)
    }
  }
  }

  // Members declared in leon.utils.Interruptible
  def interrupt(): Unit = underlying.interrupt()
  def recoverInterrupt(): Unit = underlying.recoverInterrupt()

  // Converts expression on the fly if needed, creating a string converter if needed.
  def convertExprOnTheFly(expression: Expr, withConverter: Z3StringConversion => Expr): Expr = {
    someConverter match {
      case None =>
        if(solverInvokedWithStrings || exists(e => TypeOps.exists(StringType == _)(e.getType))(expression)) { // On the fly conversion
          solverInvokedWithStrings = true
          val c = new Z3StringConversion(program)
          someConverter = Some(c)
          withConverter(c)
        } else expression
      case Some(converter) =>
        withConverter(converter)
    }
  }
  
  // Members declared in leon.solvers.Solver
  def assertCnstr(expression: Expr): Unit = {
    someConverter.map{converter => 
      import converter.Forward._
      val newExpression = convertExpr(expression)(Map())
      underlying.assertCnstr(newExpression)
    }.getOrElse{
      underlying.assertCnstr(convertExprOnTheFly(expression, _.Forward.convertExpr(expression)(Map())))
    }
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
     with Z3StringEvaluatingSolver[FairZ3Solver] {

     // Members declared in leon.solvers.z3.AbstractZ3Solver
    protected[leon] val z3cfg: _root_.z3.scala.Z3Config = underlying.z3cfg
    override def checkAssumptions(assumptions: Set[Expr]): Option[Boolean] = {
      someConverter match {
        case None => underlying.checkAssumptions(assumptions.map(e => convertExprOnTheFly(e, _.Forward.convertExpr(e)(Map()))))
        case Some(converter) =>
          underlying.checkAssumptions(assumptions map (e => converter.Forward.convertExpr(e)(Map())))
      }
    }
}

class Z3StringUnrollingSolver(context: LeonContext, program: Program, underlyingSolverConstructor: Program => Solver)
  extends Z3StringCapableSolver(context, program, (program: Program, converter: Option[Z3StringConversion]) =>
    new UnrollingSolver(context, program, underlyingSolverConstructor(program)))
  with Z3StringNaiveAssumptionSolver[UnrollingSolver]
     with Z3StringEvaluatingSolver[UnrollingSolver] {

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

