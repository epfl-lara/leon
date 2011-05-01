package cp

import Serialization._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.Common._
import purescala.{QuietReporter,DefaultReporter}
import purescala.FairZ3Solver
import purescala.Stopwatch
import Definitions.{UnsatisfiableConstraintException,UnknownConstraintException}

object Constraints {
  private val silent = true
  private def newReporter() = if (silent) new QuietReporter() else new DefaultReporter()
  private def newSolver(program : Program) = {
    val s = new FairZ3Solver(newReporter())
    s.setProgram(program)
    s
  }

  sealed trait Constraint {
    type sig
    val convertingFunction : (Seq[Expr] => sig)

    def solve : sig = {
      convertingFunction(solveExprSeq(this))
    }

    def find : Option[sig] = {
      try {
        Some(this.solve)
      } catch {
        case e: UnsatisfiableConstraintException => None
        case e: UnknownConstraintException => None
      }
    }

    def findAll : Iterator[sig] = {
      findAllExprSeq(this).map(convertingFunction(_))
    }

  }

  sealed trait OptimizingTerm
  sealed trait OptimizingTerm1[A] extends OptimizingTerm // can contain integer functions
  sealed trait OptimizingTerm2[A,B] extends OptimizingTerm

  abstract class MinConstraint(cons : Constraint, minTerm : OptimizingTerm) {
    type sig
    val convertingFunction : (Seq[Expr] => sig)

    def solve : sig = {
      convertingFunction(solveMinimizingExprSeq(cons, minTerm))
    }

    def find : Option[sig] = {
      try {
        Some(this.solve)
      } catch {
        case e: UnsatisfiableConstraintException => None
        case e: UnknownConstraintException => None
      }
    }

    def findAll : Iterator[sig] = {
      findAllMinimizingExprSeq(cons, minTerm).map(convertingFunction(_))
    } 
  }

  case class MinConstraint1[A](cons : Constraint1[A], minTerm : OptimizingTerm1[A]) extends MinConstraint(cons, minTerm) {
    type sig = A
    val convertingFunction = converterOf(cons).exprSeq2scala1[A] _
  }

  case class MinConstraint2[A,B](cons : Constraint2[A,B], minTerm : OptimizingTerm2[A,B]) extends MinConstraint(cons, minTerm) {
    type sig = (A,B)
    val convertingFunction = converterOf(cons).exprSeq2scala2[A,B] _
  }

  sealed trait Constraint1[A] extends Constraint {
    type sig = A
    val convertingFunction = converterOf(this).exprSeq2scala1[A] _

    def minimizing(minTerm : OptimizingTerm1[A]) : MinConstraint1[A] =
      MinConstraint1[A](this, minTerm)
      
    def ||(other : Constraint1[A]) : Constraint1[A] = OrConstraint1[A](this, other)
  }

  sealed trait Constraint2[A,B] extends Constraint {
    type sig = (A,B)
    val convertingFunction = converterOf(this).exprSeq2scala2[A,B] _

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

  class OrConstraint1[A](val constraints : Seq[Constraint1[A]]) extends Constraint1[A]

  object OrConstraint1 {
    def apply[A](l : Constraint1[A], r : Constraint1[A]) : Constraint1[A] = {
      new OrConstraint1[A](Seq(l,r))
    }

    def unapply[A](or : OrConstraint1[A]) : Option[Seq[Constraint1[A]]] =
      if (or == null) None else Some(or.constraints)
  }

  class OrConstraint2[A,B](val constraints : Seq[Constraint2[A,B]]) extends Constraint2[A,B]

  object OrConstraint2 {
    def apply[A,B](l : Constraint2[A,B], r : Constraint2[A,B]) : Constraint2[A,B] = {
      new OrConstraint2[A,B](Seq(l,r))
    }

    def unapply[A,B](or : OrConstraint2[A,B]) : Option[Seq[Constraint2[A,B]]] =
      if (or == null) None else Some(or.constraints)
  }

  /** Extractor for or constraints of any type signature */
  object OrConstraint {
    def unapply(constraint : Constraint) : Option[Seq[Constraint]] = constraint match {
      case OrConstraint1(cs) => Some(cs)
      case OrConstraint2(cs) => Some(cs)
      case _ => None
    }
  }

  /** Extractor for NAry constraints of any type signature */
  object NAryConstraint {
    def unapply(constraint : Constraint) : Option[Seq[Constraint]] = constraint match {
      case OrConstraint(cs) => Some(cs)
      case _ => None
    }
  }

  /********** CONSTRAINT METHODS **********/
  /** Compute the expression associated with this constraint, with De Bruijn
   * indices */
  private def exprOf(constraint : Constraint) : Expr = constraint match {
    case bc : BaseConstraint => bc.exprWithIndices
    case OrConstraint(cs) => Or(cs map exprOf)
  }

  private def programOf(constraint : Constraint) : Program = constraint match {
    case bc : BaseConstraint => bc.program
    case NAryConstraint(cs) => programOf(cs.head)
  }

  private def typesOf(constraint : Constraint) : Seq[TypeTree] = constraint match {
    case bc : BaseConstraint => bc.outputVars.map(_.getType)
    case NAryConstraint(cs) => typesOf(cs.head)
  }

  private def envOf(constraint : Constraint) : Map[Variable,Expr] = constraint match {
    case bc : BaseConstraint => bc.env
    case NAryConstraint(cs) =>
      val allEnvs = cs map (envOf(_))
      val distinctEnvs = allEnvs.distinct
      if (distinctEnvs.size > 1) {
        throw new Exception("Environments differ in constraint: \n" + distinctEnvs.mkString("\n"))
      }
      allEnvs(0)
  }

  private def converterOf(constraint : Constraint) : Converter = constraint match {
    case bc : BaseConstraint => bc.converter
    case NAryConstraint(cs) => converterOf(cs.head)
  }

  /** Compute a fresh sequence of output variables, the combined expression
   * containing those, and the constraint for the environment */
  private def combinedConstraint(constraint : Constraint) : (Seq[Identifier], Expr, Expr) = {
    val expr = exprOf(constraint)

    val outputVarTypes = typesOf(constraint)

    val freshOutputIDs = outputVarTypes.zipWithIndex.map{ case (t, idx) => FreshIdentifier("x" + idx).setType(t) }
    val deBruijnIndices = outputVarTypes.zipWithIndex.map{ case (t, idx) => DeBruijnIndex(idx).setType(t) }
    val exprWithFreshIDs = replace((deBruijnIndices zip (freshOutputIDs map (Variable(_)))).toMap, expr)

    val env = envOf(constraint)

    val inputConstraints = if (env.isEmpty) BooleanLiteral(true) else And(env.map{ case (v, e) => Equals(v, e) }.toSeq)

    (freshOutputIDs, exprWithFreshIDs, inputConstraints)
  }

  /********** SOLVING METHODS **********/
  /** Return interpretation of the constant in model if it exists, the simplest
   * value otherwise */
  private def modelValue(varId: Identifier, model: Map[Identifier, Expr]) : Expr = model.get(varId) match {
    case Some(value) => value
    case None => simplestValue(varId.getType)
  }

  /** Return a solution as a sequence of expressions */
  private def solveExprSeq(constraint : Constraint) : Seq[Expr] = {
    val solver = newSolver(programOf(constraint))

    val (freshOutputIDs, expr, inputConstraints) = combinedConstraint(constraint)

    val (outcome, model) = solver.restartAndDecideWithModel(And(expr, inputConstraints), false)

    outcome match {
      case Some(false) =>
        freshOutputIDs.map(id => modelValue(id, model))
      case Some(true) =>
        throw new UnsatisfiableConstraintException()
      case None =>
        throw new UnknownConstraintException()
    }
  }

  /** Return a solution that minimizes the given term, as a sequence of expressions */
  private def solveMinimizingExprSeq(constraint : Constraint, minTerm : OptimizingTerm) : Seq[Expr] =
    throw new Exception()

  /** Return an iterator of solutions as sequences of expressions */
  private def findAllExprSeq(constraint : Constraint) : Iterator[Seq[Expr]] = {
    val program = programOf(constraint)
    val (freshOutputIDs, expr, inputConstraints) = combinedConstraint(constraint)

    val modelIterator = solutionsIterator(program, expr, inputConstraints, freshOutputIDs.toSet)
    val exprIterator  = modelIterator.map(model => freshOutputIDs.map(id => model(id)))

    exprIterator
  }

  /** Enumerate all solutions ordered by the term to minimize, as sequences of expressions */
  private def findAllMinimizingExprSeq(constraint : Constraint, minTerm : OptimizingTerm) : Iterator[Seq[Expr]] =
    throw new Exception()

  /** Returns an iterator of interpretations for each identifier in the specified set */
  private def solutionsIterator(program : Program, predicate : Expr, inputEqualities : Expr, outputVariables : Set[Identifier]) : Iterator[Map[Identifier, Expr]] = {
    val solver = newSolver(program)
    solver.restartZ3

    new Iterator[Map[Identifier, Expr]] {

      // If nextModel is None, we do not know yet whether there is a next element
      var nextModel: Option[Option[Map[Identifier, Expr]]] = None

      // We add after finding each model the negation of the previous one
      var addedNegations: Expr = BooleanLiteral(true)

      var toCheck: Expr = And(inputEqualities, predicate)

      override def hasNext : Boolean = nextModel match {
        case None => 
          // Check whether there are any more models
          val stopwatch = new Stopwatch("hasNext", false).start
          val (outcome, model) = solver.decideWithModel(toCheck, false)
          stopwatch.stop
          stopwatch.writeToSummary
          val toReturn = (outcome match {
            case Some(false) =>
              // there is a solution, we need to complete model for nonmentioned variables
              val completeModel = outputVariables.foldLeft(model){
                case (modelSoFar, ov) => modelSoFar.get(ov) match {
                  case None =>
                    // model has to be augmented for ov
                    modelSoFar + (ov -> simplestValue(ov.getType))
                  case _ =>
                    modelSoFar
                }
              }
              nextModel = Some(Some(completeModel))
              val newModelEqualities = And(outputVariables.map(ov => Equals(Variable(ov), completeModel(ov))).toList)
              toCheck = negate(newModelEqualities)
              true
            case Some(true) =>
              // there are definitely no more solutions
              nextModel = Some(None)
              false
            case None =>
              // unknown
              nextModel = Some(None)
              false
          })
          toReturn
        case Some(None) =>
          // There are no more models
          false
        case Some(Some(map)) =>
          true
      }

      override def next() : Map[Identifier, Expr] = nextModel match {
        case None => {
          // Let's compute the next model
          val (outcome, model) = solver.decideWithModel(toCheck, false)
          val toReturn = (outcome match {
            case Some(false) =>
              // there is a solution, we need to complete model for nonmentioned variables
              val completeModel = outputVariables.foldLeft(model){
                case (modelSoFar, ov) => modelSoFar.get(ov) match {
                  case None =>
                    // model has to be augmented for ov
                    modelSoFar + (ov -> simplestValue(ov.getType))
                  case _ =>
                    modelSoFar
                }
              }

              val newModelEqualities = And(outputVariables.map(ov => Equals(Variable(ov), completeModel(ov))).toList)
              toCheck = negate(newModelEqualities)
              completeModel
            case Some(true) =>
              // Definitely no more solutions
              throw new Exception("Requesting a new model while there are no more")
            case None =>
              // Unknown
              throw new Exception("Requesting a new model while there are no more")
          })
          toReturn
        }
        case Some(Some(m)) =>
          nextModel = None
          m
        case Some(None) =>
          throw new Exception("Requesting a new model while the last result was unknown")
      }
    }
  }
}
