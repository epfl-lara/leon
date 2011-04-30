package cp

import Serialization._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.Common._
import purescala.{QuietReporter,DefaultReporter}
import purescala.FairZ3Solver
import Definitions.{UnsatisfiableConstraintException,UnknownConstraintException}

object Constraints {
  final class NotImplementedException extends Exception

  private val silent = true
  private def newReporter() = if (silent) new QuietReporter() else new DefaultReporter()
  private def newSolver() = new FairZ3Solver(newReporter())

  sealed trait Constraint

  private def modelValue(varId: Identifier, model: Map[Identifier, Expr]) : Expr = model.get(varId) match {
    case Some(value) => value
    case None => simplestValue(varId.getType)
  }

  def programOf(constraint : Constraint) : Program = constraint match {
    case bc : BaseConstraint => bc.program
    case NAryConstraint(cs) => programOf(cs.head)
  }

  def exprOf(constraint : Constraint) : Expr = constraint match {
    case bc : BaseConstraint => bc.exprWithIndices
    case OrConstraint(cs) => Or(cs map exprOf)
  }

  def typesOf(constraint : Constraint) : Seq[TypeTree] = constraint match {
    case bc : BaseConstraint => bc.outputVars.map(_.getType)
    case NAryConstraint(cs) => typesOf(cs.head)
  }

  def envOf(constraint : Constraint) : Map[Variable,Expr] = constraint match {
    case bc : BaseConstraint => bc.env
    case NAryConstraint(cs) =>
      val allEnvs = cs map (envOf(_))
      val distinctEnvs = allEnvs.distinct
      if (distinctEnvs.size > 1) {
        throw new Exception("Environments differ in constraint: \n" + distinctEnvs.mkString("\n"))
      }
      allEnvs(0)
  }

  def converterOf(constraint : Constraint) : Converter = constraint match {
    case bc : BaseConstraint => bc.converter
    case NAryConstraint(cs) => converterOf(cs.head)
  }

  private def exprSeqSolution(constraint : Constraint) : Seq[Expr] = {
    val solver = newSolver()
    val program = programOf(constraint)
    solver.setProgram(program)

    // println("My program is")
    // println(program)

    val expr = exprOf(constraint)

    // println("My expr is")
    // println(expr)

    val outputVarTypes = typesOf(constraint)

    val freshOutputIDs = outputVarTypes.zipWithIndex.map{ case (t, idx) => FreshIdentifier("x" + idx).setType(t) }
    val deBruijnIndices = outputVarTypes.zipWithIndex.map{ case (t, idx) => DeBruijnIndex(idx).setType(t) }
    val exprWithFreshIDs = replace((deBruijnIndices zip (freshOutputIDs map (Variable(_)))).toMap, expr)

    // println("Expr with fresh IDs")
    // println(exprWithFreshIDs)

    val env = envOf(constraint)

    // println("Environment")
    // println(env)

    val inputConstraints = if (env.isEmpty) BooleanLiteral(true) else And(env.map{ case (v, e) => Equals(v, e) }.toSeq)

    val (outcome, model) = solver.restartAndDecideWithModel(And(exprWithFreshIDs, inputConstraints), false)
    val exprSeq = outcome match {
      case Some(false) =>
        freshOutputIDs.map(id => modelValue(id, model))
      case Some(true) =>
        throw new UnsatisfiableConstraintException()
      case None =>
        throw new UnknownConstraintException()
    }

    // println("Solution!")
    // println(exprSeq)

    exprSeq
  }

  sealed trait Constraint1[A] extends Constraint {
    def solve : A = {
      val convertingFunction = converterOf(this).exprSeq2scala1[A] _
      convertingFunction(exprSeqSolution(this))
    }

    def ||(other : Constraint1[A]) : Constraint1[A] = OrConstraint1[A](this, other)
  }

  sealed trait Constraint2[A,B] extends Constraint {
    def ||(other : Constraint2[A,B]) : Constraint2[A,B] = OrConstraint2[A,B](this, other)
  }

  abstract class BaseConstraint(conv : Converter, serializedProg : Serialized, serializedInputVars : Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) 
    extends Constraint {

    val converter : Converter             = conv
    lazy val program : Program            = deserialize[Program](serializedProg)
    lazy val inputVars : Seq[Variable]    = deserialize[Seq[Variable]](serializedInputVars)
    lazy val outputVars : Seq[Identifier] = deserialize[Seq[Identifier]](serializedOutputVars)
    lazy val expr : Expr                  = deserialize[Expr](serializedExpr)
    lazy val env : Map[Variable,Expr]     = (inputVars zip inputVarValues).toMap

    lazy val deBruijnIndices: Seq[DeBruijnIndex] = outputVars.zipWithIndex.map{ case (v, idx) => DeBruijnIndex(idx).setType(v.getType) }
    lazy val exprWithIndices: Expr = replace(((outputVars map (Variable(_))) zip deBruijnIndices).toMap, expr)
  }

  case class BaseConstraint1[A](conv : Converter, serializedProg : Serialized, serializedInputVars : Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) 
    extends BaseConstraint(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues) with Constraint1[A]

  case class BaseConstraint2[A,B](conv : Converter, serializedProg : Serialized, serializedInputVars : Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) 
    extends BaseConstraint(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues) with Constraint2[A,B]

  class OrConstraint1[A](val exprs : Seq[Constraint1[A]]) extends Constraint1[A]

  object OrConstraint1 {
    def apply[A](l : Constraint1[A], r : Constraint1[A]) : Constraint1[A] = {
      new OrConstraint1[A](Seq(l,r))
    }

    def unapply[A](or : OrConstraint1[A]) : Option[Seq[Constraint1[A]]] =
      if (or == null) None else Some(or.exprs)
  }

  class OrConstraint2[A,B](val exprs : Seq[Constraint2[A,B]]) extends Constraint2[A,B]

  object OrConstraint2 {
    def apply[A,B](l : Constraint2[A,B], r : Constraint2[A,B]) : Constraint2[A,B] = {
      new OrConstraint2[A,B](Seq(l,r))
    }

    def unapply[A,B](or : OrConstraint2[A,B]) : Option[Seq[Constraint2[A,B]]] =
      if (or == null) None else Some(or.exprs)
  }

  /** Extractor for or constraints of any type signature */
  object OrConstraint {
    def unapply(constraint : Constraint) : Option[Seq[Constraint]] = constraint match {
      case OrConstraint1(exprs) => Some(exprs)
      case OrConstraint2(exprs) => Some(exprs)
      case _ => None
    }
  }

  /** Extractor for NAry constraints of any type signature */
  object NAryConstraint {
    def unapply(constraint : Constraint) : Option[Seq[Constraint]] = constraint match {
      case OrConstraint(exprs) => Some(exprs)
      case _ => None
    }
  }

}
