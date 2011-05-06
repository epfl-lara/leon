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
  abstract case class Term[T,R](program : Program, expr : Expr, types : Seq[TypeTree], converter : Converter) {
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

  /** Terms with one argument */
  sealed trait Term1[T1,R] extends Term[T1,R] {
    val convertingFunction = converterOf(this).exprSeq2scala1[T1] _
    type t2c = (Term1[T1,R]) => Term1[T1,Boolean]

    def minimizing(minFunc : IntTerm1[T1])(implicit asConstraint: t2c) : MinConstraint1[T1] = {
      MinConstraint1[T1](asConstraint(this), minFunc)
    }
      
    def ||(other : Constraint1[T1])(implicit asConstraint: t2c) : Constraint1[T1] = OrConstraint1[T1](asConstraint(this), other)

    def &&(other : Constraint1[T1])(implicit asConstraint: t2c) : Constraint1[T1] = AndConstraint1[T1](asConstraint(this), other)

    def unary_!(implicit asConstraint: t2c) : Constraint1[T1] = NotConstraint1[T1](asConstraint(this))

    /** function composition this ∘ other */
    def compose0[A](other : Term1[A,T1]) : Term1[A,R]       = compose_0_1_1(other, this)
    def compose0[A,B](other : Term2[A,B,T1]) : Term2[A,B,R] = compose_0_2_1(other, this)
  }

  /** Terms with two arguments */
  sealed trait Term2[T1,T2,R] extends Term[(T1,T2),R] {
    val convertingFunction = converterOf(this).exprSeq2scala2[T1,T2] _
    type t2c = (Term2[T1,T2,R]) => Term2[T1,T2,Boolean]

    def minimizing(minFunc : IntTerm2[T1,T2])(implicit asConstraint: t2c) : MinConstraint2[T1,T2] =
      MinConstraint2[T1,T2](asConstraint(this), minFunc)
      
    def ||(other : Constraint2[T1,T2])(implicit asConstraint: t2c) : Constraint2[T1,T2] = OrConstraint2[T1,T2](this, other)

    def &&(other : Constraint2[T1,T2])(implicit asConstraint: t2c) : Constraint2[T1,T2] = AndConstraint2[T1,T2](this, other)

    def unary_!(implicit asConstraint: t2c) : Constraint2[T1,T2] = NotConstraint2[T1,T2](this)

    def compose0[A](other : Term1[A, T1]) : Term2[A,T2,R] = compose_0_1_2(other, this)
    def compose1[A](other : Term1[A, T2]) : Term2[T1,A,R] = compose_1_1_2(other, this)
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

  /** Contains helper methods for constructing base terms */
  object Term {
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

  object Term1 {
    def apply[T1,R](conv : Converter, serializedProg : Serialized, serializedInputVars : Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) = {
      val (converter, program, expr, types) = Term.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new Term[T1,R](program, expr, types, converter) with Term1[T1,R]
    }

    def apply[T1,R](program : Program, expr : Expr, types : Seq[TypeTree], converter : Converter) =
      new Term[T1,R](program, expr, types, converter) with Term1[T1,R]
  }

  object Term2 {
    def apply[T1,T2,R](conv : Converter, serializedProg : Serialized, serializedInputVars : Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) = {
      val (converter, program, expr, types) = Term.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new Term[(T1,T2),R](program, expr, types, converter) with Term2[T1,T2,R]
    }

    def apply[T1,T2,R](program : Program, expr : Expr, types : Seq[TypeTree], converter : Converter) =
      new Term[(T1,T2),R](program, expr, types, converter) with Term2[T1,T2,R]
  }

  /** A constraint is just a term with Boolean range */
  type Constraint[T] = Term[T,Boolean]
  type Constraint1[T1] = Term1[T1,Boolean]
  type Constraint2[T1,T2] = Term2[T1,T2,Boolean]

  object OrConstraint1 {
    def apply[A](l : Constraint[A], r : Constraint[A]) : Constraint1[A] = (l, r) match {
      case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term1(p1,Or(ex1,ex2),ts1,conv1)
    }

    def apply[A](cs : Seq[Constraint[A]]) : Constraint1[A] = cs match {
      case s @ Seq(Term(p,ex,ts,conv), _*) => Term1(p, Or(s.map(_.expr)), ts, conv)
    }
  }

  object OrConstraint2 {
    def apply[A,B](l : Constraint[(A,B)], r : Constraint[(A,B)]) : Constraint2[A,B] = (l, r) match {
      case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term2(p1,Or(ex1,ex2),ts1,conv1)
    }

    def apply[A,B](cs : Seq[Constraint[(A,B)]]) : Constraint2[A,B] = cs match {
      case s @ Seq(Term(p,ex,ts,conv), _*) => Term2(p, Or(s.map(_.expr)), ts, conv)
    }
  }

  object AndConstraint1 {
    def apply[A](l : Constraint[A], r : Constraint[A]) : Constraint1[A] = (l, r) match {
      case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term1(p1,And(ex1,ex2),ts1,conv1)
    }

    def apply[A](cs : Seq[Constraint[A]]) : Constraint1[A] = cs match {
      case s @ Seq(Term(p,ex,ts,conv), _*) => Term1(p, And(s.map(_.expr)), ts, conv)
    }
  }

  object AndConstraint2 {
    def apply[A,B](l : Constraint[(A,B)], r : Constraint[(A,B)]) : Constraint2[A,B] = (l, r) match {
      case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term2(p1,And(ex1,ex2),ts1,conv1)
    }

    def apply[A,B](cs : Seq[Constraint[(A,B)]]) : Constraint2[A,B] = cs match {
      case s @ Seq(Term(p,ex,ts,conv), _*) => Term2(p, And(s.map(_.expr)), ts, conv)
    }
  }

  object NotConstraint1 {
    def apply[A](c : Constraint[A]) : Constraint1[A] = c match {
      case Term(p,ex,ts,conv) => Term1(p,Not(ex),ts,conv)
    }
  }

  object NotConstraint2 {
    def apply[A,B](c : Constraint[(A,B)]) : Constraint2[A,B] = c match {
      case Term(p,ex,ts,conv) => Term2(p,Not(ex),ts,conv)
    }
  }

  type IntTerm[T] = Term[T,Int]
  type IntTerm1[T1] = Term1[T1,Int]
  type IntTerm2[T1,T2] = Term2[T1,T2,Int]

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
  /** compose_i_j_k will compose f (of arity j) and g (of arity k) as "g∘f" by
   * inserting arguments of f in place of argument i of g */
  private def compose_0_1_1[T1,T2,T3](f : Term[T1,T2], g : Term[T2,T3]) : Term1[T1,T3] = {
    val (newExpr, newTypes) = compose(f, g, 0, 1, 1)
    Term1(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_2_1[T1,T2,R1,R2](f : Term[(T1,T2),R1], g : Term[R1,R2]) : Term2[T1,T2,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 2, 1)
    Term2(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_1_2[T1,R1,T2,R2](f : Term[T1,R1], g : Term[(R1,T2),R2]) : Term2[T1,T2,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 1, 2)
    Term2(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_1_2[T1,R1,T2,R2](f : Term[T1,R1], g : Term[(T2,R1),R2]) : Term2[T2,T1,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 1, 2)
    Term2(f.program, newExpr, newTypes, f.converter)
  }

  /** Compute composed expression for g∘f */
  private def compose(f : Term[_,_], g : Term[_,_], index : Int, nf : Int, ng : Int) : (Expr, Seq[TypeTree]) = (f, g) match {
    case (Term(_,ef,tf,_),Term(_,eg,tg,_)) => {
      val deBruijnF = tf.zipWithIndex.map{ case (t,i) => DeBruijnIndex(i).setType(t) }
      val deBruijnG = tg.zipWithIndex.map{ case (t,i) => DeBruijnIndex(i).setType(t) }
      assert(deBruijnF.size == nf && deBruijnG.size == ng)

      val substG : Map[Expr,Expr] = deBruijnG.drop(index + 1).map{ case d @ DeBruijnIndex(i) => (d, DeBruijnIndex(i + nf - 1).setType(d.getType)) }.toMap
      val substF : Map[Expr,Expr] = deBruijnF.map{ case d @ DeBruijnIndex(i) => (d, DeBruijnIndex(i + index).setType(d.getType)) }.toMap

      val renamedExprF = replace(substF, ef)
      val renamedExprG = replace(substG, eg)

      val indexToReplace = deBruijnG(index)
      val newExpr   = replace(Map(indexToReplace -> renamedExprF), renamedExprG)
      val newTypes  = g.types.take(index) ++ f.types ++ g.types.drop(index + nf)
      assert(newTypes.size == nf + ng - 1)
      (newExpr, newTypes)
    }
  }

  private def converterOf(term : Term[_,_]) : Converter = term.converter

  private def typesOf(term : Term[_,_]) : Seq[TypeTree] = term.types

  private def exprOf(term : Term[_,_]) : Expr = term.expr

  private def programOf(term : Term[_,_]) : Program = term.program

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
