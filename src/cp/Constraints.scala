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

  sealed trait Constraint1[A] extends Constraint {
    type sig = A
    val convertingFunction = converterOf(this).exprSeq2scala1[A] _

    def minimizing(minFunc : OptimizingFunction1[A]) : MinConstraint1[A] =
      MinConstraint1[A](this, minFunc)
      
    def ||(other : Constraint1[A]) : Constraint1[A] = OrConstraint1[A](this, other)

    def &&(other : Constraint1[A]) : Constraint1[A] = AndConstraint1[A](this, other)

    def unary_! : Constraint1[A] = NotConstraint1[A](this)
  }

  sealed trait Constraint2[A,B] extends Constraint {
    type sig = (A,B)
    val convertingFunction = converterOf(this).exprSeq2scala2[A,B] _

    def minimizing(minFunc : OptimizingFunction2[A,B]) : MinConstraint2[A,B] =
      MinConstraint2[A,B](this, minFunc)
      
    def ||(other : Constraint2[A,B]) : Constraint2[A,B] = OrConstraint2[A,B](this, other)

    def &&(other : Constraint2[A,B]) : Constraint2[A,B] = AndConstraint2[A,B](this, other)

    def unary_! : Constraint2[A,B] = NotConstraint2[A,B](this)

    // def proj0 : Constraint1[A] = proj0(this)
  }

  abstract case class BaseConstraint(converter : Converter, program : Program, expr : Expr, types : Seq[TypeTree]) extends Constraint

  object BaseConstraint1 {
    def apply[A](conv : Converter, serializedProg : Serialized, serializedInputVars : Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) = {
      val program : Program             = deserialize[Program](serializedProg)
      val inputVars : Seq[Variable]     = deserialize[Seq[Variable]](serializedInputVars)
      val outputVars : Seq[Identifier]  = deserialize[Seq[Identifier]](serializedOutputVars)
      val initialExpr : Expr            = deserialize[Expr](serializedExpr)

      val env : Map[Expr,Expr]                 = (inputVars zip inputVarValues).toMap
      val deBruijnIndices: Seq[DeBruijnIndex]  = outputVars.zipWithIndex.map{ case (v, idx) => DeBruijnIndex(idx).setType(v.getType) }
      val exprWithIndices: Expr                = replace(((outputVars map (Variable(_))) zip deBruijnIndices).toMap, initialExpr)
      val expr : Expr                          = replace(env, exprWithIndices)
      val types : Seq[TypeTree]                = outputVars.map(_.getType)
      new BaseConstraint(conv, program, expr, types) with Constraint1[A]
    }
  }

  object BaseConstraint2 {
    def apply[A,B](conv : Converter, serializedProg : Serialized, serializedInputVars : Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) = {
      val program : Program             = deserialize[Program](serializedProg)
      val inputVars : Seq[Variable]     = deserialize[Seq[Variable]](serializedInputVars)
      val outputVars : Seq[Identifier]  = deserialize[Seq[Identifier]](serializedOutputVars)
      val initialExpr : Expr            = deserialize[Expr](serializedExpr)

      val env : Map[Expr,Expr]                 = (inputVars zip inputVarValues).toMap
      val deBruijnIndices: Seq[DeBruijnIndex]  = outputVars.zipWithIndex.map{ case (v, idx) => DeBruijnIndex(idx).setType(v.getType) }
      val exprWithIndices: Expr                = replace(((outputVars map (Variable(_))) zip deBruijnIndices).toMap, initialExpr)
      val expr : Expr                          = replace(env, exprWithIndices)
      val types : Seq[TypeTree]                = outputVars.map(_.getType)
      new BaseConstraint(conv, program, expr, types) with Constraint2[A,B]
    }
  }

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

  class AndConstraint1[A](val constraints : Seq[Constraint1[A]]) extends Constraint1[A]

  object AndConstraint1 {
    def apply[A](l : Constraint1[A], r : Constraint1[A]) : Constraint1[A] = {
      new AndConstraint1[A](Seq(l,r))
    }

    def unapply[A](and : AndConstraint1[A]) : Option[Seq[Constraint1[A]]] =
      if (and == null) None else Some(and.constraints)
  }

  class AndConstraint2[A,B](val constraints : Seq[Constraint2[A,B]]) extends Constraint2[A,B]

  object AndConstraint2 {
    def apply[A,B](l : Constraint2[A,B], r : Constraint2[A,B]) : Constraint2[A,B] = {
      new AndConstraint2[A,B](Seq(l,r))
    }

    def unapply[A,B](and : AndConstraint2[A,B]) : Option[Seq[Constraint2[A,B]]] =
      if (and == null) None else Some(and.constraints)
  }

  /** Extractor for and constraints of any type signature */
  object AndConstraint {
    def unapply(constraint : Constraint) : Option[Seq[Constraint]] = constraint match {
      case AndConstraint1(cs) => Some(cs)
      case AndConstraint2(cs) => Some(cs)
      case _ => None
    }
  }

  case class NotConstraint1[A](constraint : Constraint1[A]) extends Constraint1[A]
  case class NotConstraint2[A,B](constraint : Constraint2[A,B]) extends Constraint2[A,B]

  /** Extractor for `not' constraints of any type signature */
  object NotConstraint {
    def unapply(constraint : Constraint) : Option[Constraint] = constraint match {
      case NotConstraint1(c) => Some(c)
      case NotConstraint2(c) => Some(c)
      case _ => None
    }
  }

  /** Extractor for NAry constraints of any type signature */
  object NAryConstraint {
    def unapply(constraint : Constraint) : Option[Seq[Constraint]] = constraint match {
      case OrConstraint(cs) => Some(cs)
      case AndConstraint(cs) => Some(cs)
      case _ => None
    }
  }

  /** Extractor for unary constraints of any type signature */
  object UnaryConstraint {
    def unapply(constraint : Constraint) : Option[Constraint] = constraint match {
      case NotConstraint(c) => Some(c)
      case _ => None
    }
  }

  sealed trait OptimizingFunction
  sealed trait OptimizingFunction1[A] extends OptimizingFunction // can contain integer functions
  sealed trait OptimizingFunction2[A,B] extends OptimizingFunction

  abstract case class BaseOptimizingFunction(converter : Converter, program : Program, expr : Expr, types : Seq[TypeTree]) extends OptimizingFunction

  object BaseOptimizingFunction1 {
    def apply[A](conv : Converter, serializedProg : Serialized, serializedInputVars : Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) = {
      val program : Program             = deserialize[Program](serializedProg)
      val inputVars : Seq[Variable]     = deserialize[Seq[Variable]](serializedInputVars)
      val outputVars : Seq[Identifier]  = deserialize[Seq[Identifier]](serializedOutputVars)
      val initialExpr : Expr            = deserialize[Expr](serializedExpr)

      val env : Map[Expr,Expr]                 = (inputVars zip inputVarValues).toMap
      val deBruijnIndices: Seq[DeBruijnIndex]  = outputVars.zipWithIndex.map{ case (v, idx) => DeBruijnIndex(idx).setType(v.getType) }
      val exprWithIndices: Expr                = replace(((outputVars map (Variable(_))) zip deBruijnIndices).toMap, initialExpr)
      val expr : Expr                          = replace(env, exprWithIndices)
      val types : Seq[TypeTree]                = outputVars.map(_.getType)
      new BaseOptimizingFunction(conv, program, expr, types) with OptimizingFunction1[A]
    }
  }

  object BaseOptimizingFunction2 {
    def apply[A,B](conv : Converter, serializedProg : Serialized, serializedInputVars : Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) = {
      val program : Program             = deserialize[Program](serializedProg)
      val inputVars : Seq[Variable]     = deserialize[Seq[Variable]](serializedInputVars)
      val outputVars : Seq[Identifier]  = deserialize[Seq[Identifier]](serializedOutputVars)
      val initialExpr : Expr            = deserialize[Expr](serializedExpr)

      val env : Map[Expr,Expr]                 = (inputVars zip inputVarValues).toMap
      val deBruijnIndices: Seq[DeBruijnIndex]  = outputVars.zipWithIndex.map{ case (v, idx) => DeBruijnIndex(idx).setType(v.getType) }
      val exprWithIndices: Expr                = replace(((outputVars map (Variable(_))) zip deBruijnIndices).toMap, initialExpr)
      val expr : Expr                          = replace(env, exprWithIndices)
      val types : Seq[TypeTree]                = outputVars.map(_.getType)
      new BaseOptimizingFunction(conv, program, expr, types) with OptimizingFunction2[A,B]
    }
  }

  abstract class MinConstraint(cons : Constraint, minFunc : OptimizingFunction) {
    type sig
    val convertingFunction : (Seq[Expr] => sig)

    def solve : sig = {
      convertingFunction(solveMinimizingExprSeq(cons, minFunc))
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
      findAllMinimizingExprSeq(cons, minFunc).map(convertingFunction(_))
    } 
  }

  case class MinConstraint1[A](cons : Constraint1[A], minFunc : OptimizingFunction1[A]) extends MinConstraint(cons, minFunc) {
    type sig = A
    val convertingFunction = converterOf(cons).exprSeq2scala1[A] _
  }

  case class MinConstraint2[A,B](cons : Constraint2[A,B], minFunc : OptimizingFunction2[A,B]) extends MinConstraint(cons, minFunc) {
    type sig = (A,B)
    val convertingFunction = converterOf(cons).exprSeq2scala2[A,B] _
  }

  /********** OPTIMIZING FUNCTION METHODS **********/
  /** Compute the expression associated with this function, with De Bruijn
   * indices */
  private def exprOf(function : OptimizingFunction) : Expr = function match {
    case BaseOptimizingFunction(_,_,expr,_) => expr
  }

  private def typesOf(function : OptimizingFunction) : Seq[TypeTree] = function match {
    case BaseOptimizingFunction(_,_,_,types) => types
  }

  /********** CONSTRAINT METHODS **********/
  /** Compute the expression associated with this constraint, with De Bruijn
   * indices */
  private def exprOf(constraint : Constraint) : Expr = constraint match {
    case BaseConstraint(_,_,expr,_) => expr
    case NotConstraint(c) => Not(exprOf(c))
    case OrConstraint(cs) => Or(cs map exprOf)
    case AndConstraint(cs) => And(cs map exprOf)
  }

  private def programOf(constraint : Constraint) : Program = constraint match {
    case BaseConstraint(_,program,_,_) => program
    case UnaryConstraint(c) => programOf(c)
    case NAryConstraint(cs) => programOf(cs.head)
  }

  private def typesOf(constraint : Constraint) : Seq[TypeTree] = constraint match {
    case BaseConstraint(_,_,_,types) => types
    case UnaryConstraint(c) => typesOf(c)
    case NAryConstraint(cs) => typesOf(cs.head)
  }

  private def converterOf(constraint : Constraint) : Converter = constraint match {
    case BaseConstraint(converter,_,_,_) => converter
    case UnaryConstraint(c) => converterOf(c)
    case NAryConstraint(cs) => converterOf(cs.head)
  }

  /** Compute a fresh sequence of output variables and the combined expression
   * containing those */
  private def combineConstraint(constraint : Constraint) : (Seq[Identifier], Expr) = {
    val expr = exprOf(constraint)

    val outputVarTypes = typesOf(constraint)

    val freshOutputIDs = outputVarTypes.zipWithIndex.map{ case (t, idx) => FreshIdentifier("x" + idx).setType(t) }
    val deBruijnIndices = outputVarTypes.zipWithIndex.map{ case (t, idx) => DeBruijnIndex(idx).setType(t) }
    val exprWithFreshIDs = replace((deBruijnIndices zip (freshOutputIDs map (Variable(_)))).toMap, expr)

    (freshOutputIDs, exprWithFreshIDs)
  }

  // def proj0[A,B](constraint : Constraint2[A,B]) : Constraint1[A] = constraint match {
  //   case bc : BaseConstraint => 
  // }

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

    val (freshOutputIDs, expr) = combineConstraint(constraint)

    val (outcome, model) = solver.restartAndDecideWithModel(expr, false)

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
  private def solveMinimizingExprSeq(constraint : Constraint, minFunc : OptimizingFunction) : Seq[Expr] = {
    val program = programOf(constraint)
    val (freshOutputIDs, expr) = combineConstraint(constraint)
    val minExprWithIndices = exprOf(minFunc)

    val funcSignature = typesOf(minFunc)
    val deBruijnIndices = funcSignature.zipWithIndex.map{ case (t, idx) => DeBruijnIndex(idx).setType(t) }
    val minExprWithIDs = replace((deBruijnIndices zip (freshOutputIDs map (Variable(_)))).toMap, minExprWithIndices)

    val (model, value) = minimizingModelAndValue(program, expr, freshOutputIDs, minExprWithIDs)
    model
  }

  /** Return an iterator of solutions as sequences of expressions */
  private def findAllExprSeq(constraint : Constraint) : Iterator[Seq[Expr]] = {
    val program = programOf(constraint)
    val (freshOutputIDs, expr) = combineConstraint(constraint)

    val modelIterator = solutionsIterator(program, expr, freshOutputIDs.toSet)
    val exprIterator  = modelIterator.map(model => freshOutputIDs.map(id => model(id)))

    exprIterator
  }

  /** Enumerate all solutions ordered by the term to minimize, as sequences of expressions */
  private def findAllMinimizingExprSeq(constraint : Constraint, minFunc : OptimizingFunction) : Iterator[Seq[Expr]] = {
    val program = programOf(constraint)
    val (freshOutputIDs, expr) = combineConstraint(constraint)
    val minExprWithIndices = exprOf(minFunc)

    val funcSignature = typesOf(minFunc)
    val deBruijnIndices = funcSignature.zipWithIndex.map{ case (t, idx) => DeBruijnIndex(idx).setType(t) }
    val minExprWithIDs = replace((deBruijnIndices zip (freshOutputIDs map (Variable(_)))).toMap, minExprWithIndices)

    findAllMinimizingExprSeq(program, expr, freshOutputIDs, minExprWithIDs, None)
  }

  private def findAllMinimizingExprSeq(program : Program, expr : Expr, outputVars : Seq[Identifier], minExpr : Expr, minExprBound : Option[Int]) : Iterator[Seq[Expr]] = {
    try {
      val toCheck = minExprBound match {
        case None => expr
        case Some(b) => And(expr, GreaterThan(minExpr, IntLiteral(b)))
      }
      // purescala.Settings.reporter.info("Now calling findAllMinimizing with " + toCheck)
      val minValue = minimizingModelAndValue(program, toCheck, outputVars, minExpr)._2

      val minValConstraint    = And(expr, Equals(minExpr, IntLiteral(minValue)))
      val minValModelIterator = solutionsIterator(program, minValConstraint, outputVars.toSet)
      val minValExprIterator  = minValModelIterator.map(model => outputVars.map(id => model(id)))

      minValExprIterator ++ findAllMinimizingExprSeq(program, expr, outputVars, minExpr, Some(minValue))
    } catch {
      case e: UnsatisfiableConstraintException  => Iterator[Seq[Expr]]()
      case e: UnknownConstraintException        => Iterator[Seq[Expr]]()
    }
  }


  private def minimizingModelAndValue(program : Program, expr : Expr, outputVars : Seq[Identifier], minExpr : Expr) : (Seq[Expr], Int) = {
    def stop(lo : Option[Int], hi : Int) : Boolean = lo match {
      case Some(l) => hi - l <= 2
      case None => false
    }
    
    val solver = newSolver(program)

    /* invariant : lo is always stricly less than any sat. minExpr assignment,
     * and there is always a sat. assignment less than hi */
    def minAux(pivot : Int, lo : Option[Int], hi : Int) : (Map[Identifier, Expr], Int) = {
      // println("Iterating:")
      // println("  lo     : " + (lo match { case Some(l) => l; case None => "-inf"}))
      // println("  pivot  : " + pivot)
      // println("  hi     : " + hi)
      // println
      val toCheck = expr :: LessEquals(minExpr, IntLiteral(pivot)) :: Nil
      val (outcome, model) = solver.restartAndDecideWithModel(And(toCheck), false)

      outcome match {
        case Some(false) =>
          // there is a satisfying assignment
          if (stop(lo, hi)) {
            (model, pivot)
          } else {
            lo match {
              case None =>
                // lower bound is -inf
                minAux(
                  if (pivot >= 0) -1 else pivot * 2,
                  None,
                  pivot + 1
                )
              case Some(lv) =>
                minAux(
                  lv + (pivot + 1 - lv) / 2,
                  lo,
                  pivot + 1
                )
            }
          }
        case _ =>
          // new lo is pivot
          minAux(
            pivot + (hi - pivot) / 2,
            Some(pivot),
            hi
          )
      }
    }

    // We declare a variable to hold the value to minimize:
    val minExprID = purescala.Common.FreshIdentifier("minExpr").setType(purescala.TypeTrees.Int32Type)

    solver.restartAndDecideWithModel(And(expr :: Equals(minExpr, Variable(minExprID)) :: Nil), false) match {
      case (Some(false), model) =>
        // there is a satisfying assignment
        val minExprVal = modelValue(minExprID, model) match {
          case IntLiteral(i) => i
          case e => scala.Predef.error("Unexpected value for term to minimize : " + e)
        }

        val (optimalModel, optimalValue) = minAux(minExprVal - 1, None, minExprVal + 1)
        (outputVars.map(v => modelValue(v, optimalModel)), optimalValue)
      case (Some(true), _) =>
        throw new UnsatisfiableConstraintException()
      case _ =>
        throw new UnknownConstraintException()
    }
  }
  /** Returns an iterator of interpretations for each identifier in the specified set */
  private def solutionsIterator(program : Program, predicate : Expr, outputVariables : Set[Identifier]) : Iterator[Map[Identifier, Expr]] = {
    val solver = newSolver(program)
    solver.restartZ3

    new Iterator[Map[Identifier, Expr]] {

      // If nextModel is None, we do not know yet whether there is a next element
      var nextModel: Option[Option[Map[Identifier, Expr]]] = None

      // We add after finding each model the negation of the previous one
      var addedNegations: Expr = BooleanLiteral(true)

      var toCheck: Expr = predicate

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
