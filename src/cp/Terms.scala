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

object Terms {
  /** Terms are functions with domain T (which can be a tuple) and range R */
  sealed trait Term[T,R] {
    /** The converting function defines how Expr values returned by the solver
     * will be converted back to Scala values */
    val convertingFunction : (Seq[Expr] => T)

    def solve(implicit asConstraint: (R) => Boolean) : T = {
      convertingFunction(solveExprSeq(this))
    }

    def find(implicit asConstraint: (R) => Boolean) : Option[T] = {
      try {
        Some(this.solve)
      } catch {
        case e: UnsatisfiableConstraintException => None
        case e: UnknownConstraintException => None
      }
    }

    def findAll(implicit asConstraint: (R) => Boolean) : Iterator[T] = {
      findAllExprSeq(this).map(convertingFunction(_))
    }
  }

  /** Terms of one argument */
  sealed trait Term1[T1,R] extends Term[T1,R] {
    val convertingFunction = converterOf(this).exprSeq2scala1[T1] _
    type t2c = (Term1[T1,R]) => Term1[T1,Boolean]

    def minimizing(minFunc : IntTerm1[T1])(implicit asConstraint: t2c) : MinConstraint1[T1] = {
      MinConstraint1[T1](asConstraint(this), minFunc)
    }
      
    def ||(other : Constraint1[T1])(implicit asConstraint: t2c) : Constraint1[T1] = OrConstraint1[T1](asConstraint(this), other)

    def &&(other : Constraint1[T1])(implicit asConstraint: t2c) : Constraint1[T1] = AndConstraint1[T1](asConstraint(this), other)

    def unary_!(implicit asConstraint: t2c) : Constraint1[T1] = NotConstraint1[T1](asConstraint(this))
  }

  /** Terms of two arguments */
  sealed trait Term2[T1,T2,R] extends Term[(T1,T2),R] {
    val convertingFunction = converterOf(this).exprSeq2scala2[T1,T2] _
    type t2c = (Term2[T1,T2,R]) => Term2[T1,T2,Boolean]

    def minimizing(minFunc : IntTerm2[T1,T2])(implicit asConstraint: t2c) : MinConstraint2[T1,T2] =
      MinConstraint2[T1,T2](asConstraint(this), minFunc)
      
    def ||(other : Constraint2[T1,T2])(implicit asConstraint: t2c) : Constraint2[T1,T2] = OrConstraint2[T1,T2](this, other)

    def &&(other : Constraint2[T1,T2])(implicit asConstraint: t2c) : Constraint2[T1,T2] = AndConstraint2[T1,T2](this, other)

    def unary_!(implicit asConstraint: t2c) : Constraint2[T1,T2] = NotConstraint2[T1,T2](this)
  }

    /*  this is for Constraint2[A,B]
    def proj0 : Constraint1[A] = this.asInstanceOf[Constraint] match {
      case BaseTerm(conv,pr,ex,ts) => {
        val deBruijnIndices = ts.zipWithIndex.map{ case (t,idx) => DeBruijnIndex(idx).setType(t) }
        val freshIDs = deBruijnIndices.tail.zipWithIndex.map{ case (dbi, i) => FreshIdentifier("x" + i).setType(dbi.getType) }
        val subst = deBruijnIndices.tail.zip(freshIDs map (Variable)).toMap[Expr,Expr]
        new BaseTerm[Boolean](conv, pr, replace(subst, ex), ts.take(1)) with Constraint1[A]
      }
      case NotConstraint2(c) => NotConstraint1[A](c.asInstanceOf[Constraint2[A,B]].proj0)
      case OrConstraint2(cs) => OrConstraint1[A](cs map (c => c.asInstanceOf[Constraint2[A,B]].proj0))
      case AndConstraint2(cs) => AndConstraint1[A](cs map (c => c.asInstanceOf[Constraint2[A,B]].proj0))
      case _ => error("Cannot reach this")
    }
    */

  /** A base term corresponds to an expression extracted from Scala code. It
   * holds the expression with De Bruijn indices */
  abstract case class BaseTerm[T,R](converter : Converter, program : Program, expr : Expr, types : Seq[TypeTree]) extends Term[T,R]

  /** Contains helper methods for constructing base terms */
  object BaseTerm {
    def processArgs(converter : Converter, serializedProg : Serialized, serializedInputVars : Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) : (Converter,Program,Expr,Seq[TypeTree]) = {
      val program : Program             = deserialize[Program](serializedProg)
      val inputVars : Seq[Variable]     = deserialize[Seq[Variable]](serializedInputVars)
      val outputVars : Seq[Identifier]  = deserialize[Seq[Identifier]](serializedOutputVars)
      val initialExpr : Expr            = deserialize[Expr](serializedExpr)

      val env : Map[Expr,Expr]                 = (inputVars zip inputVarValues).toMap
      val deBruijnIndices: Seq[DeBruijnIndex]  = outputVars.zipWithIndex.map{ case (v, idx) => DeBruijnIndex(idx).setType(v.getType) }
      val exprWithIndices: Expr                = replace(((outputVars map (Variable(_))) zip deBruijnIndices).toMap, initialExpr)

      val expr : Expr                          = replace(env, exprWithIndices)
      val types : Seq[TypeTree]                = outputVars.map(_.getType)
      (converter, program, expr, types)
    }
  }

  /** A constraint is just a term with Boolean range */
  type Constraint[T] = Term[T,Boolean]
  type Constraint1[T1] = Term1[T1,Boolean]
  type Constraint2[T1,T2] = Term2[T1,T2,Boolean]

  object BaseConstraint1 {
    def apply[A](conv : Converter, serializedProg : Serialized, serializedInputVars : Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) = {
      val (converter, program, expr, types) = BaseTerm.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new BaseTerm[A,Boolean](converter, program, expr, types) with Constraint1[A]
    }
  }

  object BaseConstraint2 {
    def apply[A,B](conv : Converter, serializedProg : Serialized, serializedInputVars : Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) = {
      val (converter, program, expr, types) = BaseTerm.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new BaseTerm[(A,B),Boolean](converter, program, expr, types) with Constraint2[A,B]
    }
  }

  abstract case class OrConstraint[A](val constraints : Seq[Constraint[A]]) extends Constraint[A]

  object OrConstraint1 {
    def apply[A](l : Constraint1[A], r : Constraint1[A]) : Constraint1[A] = {
      new OrConstraint[A](Seq(l,r)) with Constraint1[A]
    }

    def apply[A](cs : Seq[Constraint1[A]]) : Constraint1[A] = {
      new OrConstraint[A](cs) with Constraint1[A]
    }

    def unapply[A](or : OrConstraint[A]) : Option[Seq[Constraint[A]]] =
      if (or == null) None else Some(or.constraints)
  }

  object OrConstraint2 {
    def apply[A,B](l : Constraint2[A,B], r : Constraint2[A,B]) : Constraint2[A,B] = {
      new OrConstraint[(A,B)](Seq(l,r)) with Constraint2[A,B]
    }

    def apply[A,B](cs : Seq[Constraint2[A,B]]) : Constraint2[A,B] = {
      new OrConstraint[(A,B)](cs) with Constraint2[A,B]
    }

    def unapply(or : OrConstraint[_]) : Option[Seq[Constraint[_]]] =
      if (or == null) None else Some(or.constraints)
  }

  abstract case class AndConstraint[A](val constraints : Seq[Constraint[A]]) extends Constraint[A]

  object AndConstraint1 {
    def apply[A](l : Constraint1[A], r : Constraint1[A]) : Constraint1[A] =
      new AndConstraint[A](Seq(l,r)) with Constraint1[A]

    def apply[A](cs : Seq[Constraint1[A]]) : Constraint1[A] =
      new AndConstraint[A](cs) with Constraint1[A]

    def unapply[A](and : AndConstraint[A]) : Option[Seq[Constraint[A]]] =
      if (and == null) None else Some(and.constraints)
  }

  object AndConstraint2 {
    def apply[A,B](l : Constraint2[A,B], r : Constraint2[A,B]) : Constraint2[A,B] =
      new AndConstraint[(A,B)](Seq(l,r)) with Constraint2[A,B]

    def apply[A,B](cs : Seq[Constraint2[A,B]]) : Constraint2[A,B] =
      new AndConstraint[(A,B)](cs) with Constraint2[A,B]

    def unapply(and : AndConstraint[_]) : Option[Seq[Constraint[_]]] =
      if (and == null) None else Some(and.constraints)
  }

  abstract case class NotConstraint[A](constraint : Constraint[A]) extends Constraint[A]
  object NotConstraint1 {
    def apply[A](c : Constraint1[A]) : Constraint1[A] =
      new NotConstraint[A](c) with Constraint1[A]

    def unapply[A](not : NotConstraint[A]) : Option[Constraint[A]] =
      if (not == null) None else Some(not.constraint)
  }
  object NotConstraint2 {
    def apply[A,B](c : Constraint2[A,B]) : Constraint2[A,B] =
      new NotConstraint[(A,B)](c) with Constraint2[A,B]

    def unapply[A](not : NotConstraint[A]) : Option[Constraint[A]] =
      if (not == null) None else Some(not.constraint)
  }

  type IntTerm[T] = Term[T,Int]
  type IntTerm1[T1] = Term1[T1,Int]
  type IntTerm2[T1,T2] = Term2[T1,T2,Int]

  object BaseIntTerm1 {
    def apply[A](conv : Converter, serializedProg : Serialized, serializedInputVars : Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) = {
      val (converter, program, expr, types) = BaseTerm.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new BaseTerm[A,Int](converter, program, expr, types) with IntTerm1[A]
    }
  }

  object BaseIntTerm2 {
    def apply[A,B](conv : Converter, serializedProg : Serialized, serializedInputVars : Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) = {
      val (converter, program, expr, types) = BaseTerm.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new BaseTerm[(A,B),Int](converter, program, expr, types) with IntTerm2[A,B]
    }
  }

  /** Extractor for NAry terms of any type signature */
  object NAryTerm {
    def unapply(term : Term[_,_]) : Option[Seq[Term[_,_]]] = term match {
      case OrConstraint(cs) => Some(cs)
      case AndConstraint(cs) => Some(cs)
      case _ => None
    }
  }

  /** Extractor for unary terms of any type signature */
  object UnaryTerm {
    def unapply(term : Term[_,_]) : Option[Term[_,_]] = term match {
      case NotConstraint(c) => Some(c)
      case _ => None
    }
  }

  /** This construct represents a constraint with an expression to minimize */
  abstract class MinConstraint[T](cons : Constraint[_], minFunc : IntTerm[_]) {
    val convertingFunction : (Seq[Expr] => T)

    def solve : T = {
      convertingFunction(solveMinimizingExprSeq(cons, minFunc))
    }

    def find : Option[T] = {
      try {
        Some(this.solve)
      } catch {
        case e: UnsatisfiableConstraintException => None
        case e: UnknownConstraintException => None
      }
    }

    def findAll : Iterator[T] = {
      findAllMinimizingExprSeq(cons, minFunc).map(convertingFunction(_))
    } 
  }

  case class MinConstraint1[T](cons : Constraint1[T], minFunc : IntTerm1[T]) extends MinConstraint[T](cons, minFunc) {
    val convertingFunction = converterOf(cons).exprSeq2scala1[T] _
  }

  case class MinConstraint2[T1,T2](cons : Constraint2[T1,T2], minFunc : IntTerm2[T1,T2]) extends MinConstraint[(T1,T2)](cons, minFunc) {
    val convertingFunction = converterOf(cons).exprSeq2scala2[T1,T2] _
  }

  /********** TERM METHODS **********/
  private def converterOf(term : Term[_,_]) : Converter = term match {
    case BaseTerm(converter,_,_,_) => converter
    case UnaryTerm(c) => converterOf(c)
    case NAryTerm(cs) => converterOf(cs.head)
  }

  private def typesOf(term : Term[_,_]) : Seq[TypeTree] = term match {
    case BaseTerm(_,_,_,types) => types
    case UnaryTerm(c) => typesOf(c)
    case NAryTerm(cs) => typesOf(cs.head)
  }

  private def exprOf(term : Term[_,_]) : Expr = term match {
    case BaseTerm(_,_,expr,_) => expr
    case NotConstraint(c) => Not(exprOf(c))
    case OrConstraint(cs) => Or(cs map exprOf)
    case AndConstraint(cs) => And(cs map exprOf)
    case _ => error("here is what i couldn't match: " + term)
  }

  private def programOf(term : Term[_,_]) : Program = term match {
    case BaseTerm(_,program,_,_) => program
    case UnaryTerm(c) => programOf(c)
    case NAryTerm(cs) => programOf(cs.head)
  }

  /** Compute a fresh sequence of output variables and the combined expression
   * containing those */
  private def combineConstraint(constraint : Constraint[_]) : (Seq[Identifier], Expr) = {
    val expr = exprOf(constraint)

    val outputVarTypes = typesOf(constraint)

    val freshOutputIDs = outputVarTypes.zipWithIndex.map{ case (t, idx) => FreshIdentifier("x" + idx).setType(t) }
    val deBruijnIndices = outputVarTypes.zipWithIndex.map{ case (t, idx) => DeBruijnIndex(idx).setType(t) }
    val exprWithFreshIDs = replace((deBruijnIndices zip (freshOutputIDs map (Variable(_)))).toMap, expr)

    (freshOutputIDs, exprWithFreshIDs)
  }

  /********** SOLVING METHODS **********/

  private val silent = true
  private def newReporter() = if (silent) new QuietReporter() else new DefaultReporter()
  private def newSolver(program : Program) = {
    val s = new FairZ3Solver(newReporter())
    s.setProgram(program)
    s
  }

  /** Return interpretation of the constant in model if it exists, the simplest
   * value otherwise */
  private def modelValue(varId: Identifier, model: Map[Identifier, Expr]) : Expr = model.get(varId) match {
    case Some(value) => value
    case None => simplestValue(varId.getType)
  }

  /** Return a solution as a sequence of expressions */
  private def solveExprSeq(c : Term[_,_]) : Seq[Expr] = {
    val constraint = c.asInstanceOf[Constraint[_]]
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
  private def solveMinimizingExprSeq(constraint : Constraint[_], minFunc : IntTerm[_]) : Seq[Expr] = {
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
  private def findAllExprSeq(c : Term[_,_]) : Iterator[Seq[Expr]] = {
    val constraint = c.asInstanceOf[Constraint[_]]
    val program = programOf(constraint)
    val (freshOutputIDs, expr) = combineConstraint(constraint)

    val modelIterator = solutionsIterator(program, expr, freshOutputIDs.toSet)
    val exprIterator  = modelIterator.map(model => freshOutputIDs.map(id => model(id)))

    exprIterator
  }

  /** Enumerate all solutions ordered by the term to minimize, as sequences of expressions */
  private def findAllMinimizingExprSeq(constraint : Constraint[_], minFunc : IntTerm[_]) : Iterator[Seq[Expr]] = {
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
