package cp

import Serialization._
import Definitions.{UnsatisfiableConstraintException,UnknownConstraintException}
import ConstraintSolving._
import LTrees._

import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.Common._

object Terms {
  /** Terms are functions with domain T (which can be a tuple) and range R */
  abstract class Term[T,R](val program : Program, val expr : Expr, val types : Seq[TypeTree], val converter : Converter) {
    /** The converting function defines how Expr values returned by the solver
     * will be converted back to Scala values */
    val convertingFunction : (Seq[Expr] => T)
    val evaluator : (Seq[Expr]) => R

    def solve(implicit asConstraint: (Term[T,R]) => Term[T,Boolean]) : T = {
      convertingFunction(solveExprSeq(asConstraint(this)))
    }

    def find(implicit asConstraint: (Term[T,R]) => Term[T,Boolean]) : Option[T] = {
      try {
        Some(this.solve)
      } catch {
        case e: UnsatisfiableConstraintException => None
        case e: UnknownConstraintException => None
      }
    }

    def findAll(implicit asConstraint: (Term[T,R]) => Term[T,Boolean]) : Iterator[T] = {
      findAllExprSeq(asConstraint(this)).map(convertingFunction(_))
    }

    // def lazyFindAll(implicit asConstraint: (Term[T,R]) => Constraint[T]): LIterator[T] = {
    //   new LIterator((l: L[T]) => asConstraint(this))
    // }
  }

  def removeGuard(g: Identifier): Unit = {
    GlobalContext.kill(g)
    val noMoreLive = Not(Variable(g))
    GlobalContext.enqueueAssert(noMoreLive)
  }

  def createL[T](constraint: Constraint[_], constant: Identifier, guard: Identifier): L[T] = {
    val handler = new LHandler[T] {
      val converter: Converter = constraint.converter
      def enqueueAsForced(ids: Seq[Identifier], values: Seq[Expr]): Unit = {
        val haveValues = And((ids zip values) map {
          case (i, v) => Equals(Variable(i), v)
        })
        GlobalContext.enqueueAssert(haveValues)
        removeGuard(guard)
      }
    }
    new L[T](handler, Seq(constant))
  }

  def constantsAndGuards[T](constraint: Constraint[T]): (Seq[Identifier], Seq[Identifier]) = {
    val (newConsts, newExpr) = combineConstraint(constraint)

    GlobalContext.initializeIfNeeded(constraint.program)

    val newGuards = newConsts map (nc => FreshIdentifier("live", true).setType(BooleanType))
    newGuards foreach GlobalContext.addLive

    val toAssert = Implies(Or(newGuards map (ng => Variable(ng))), newExpr)
    if (GlobalContext.checkAssumptions(toAssert)) {
      // we can return variables and their guards
      (newConsts, newGuards)
    } else {
      // constraint is not satisfiable, remove guard from context
      newGuards foreach removeGuard
      throw new UnsatisfiableConstraintException
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

  /** GENERATED CODE: */

  /** Type aliases for terms with boolean and integer range */
  type Constraint[T] = Term[T,Boolean]
  type Constraint1[T1] = Term1[T1,Boolean]
  type Constraint2[T1,T2] = Term2[T1,T2,Boolean]
  type Constraint3[T1,T2,T3] = Term3[T1,T2,T3,Boolean]
  type Constraint4[T1,T2,T3,T4] = Term4[T1,T2,T3,T4,Boolean]
  type Constraint5[T1,T2,T3,T4,T5] = Term5[T1,T2,T3,T4,T5,Boolean]
  type Constraint6[T1,T2,T3,T4,T5,T6] = Term6[T1,T2,T3,T4,T5,T6,Boolean]
  type Constraint7[T1,T2,T3,T4,T5,T6,T7] = Term7[T1,T2,T3,T4,T5,T6,T7,Boolean]
  type Constraint8[T1,T2,T3,T4,T5,T6,T7,T8] = Term8[T1,T2,T3,T4,T5,T6,T7,T8,Boolean]
  type Constraint9[T1,T2,T3,T4,T5,T6,T7,T8,T9] = Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,Boolean]
  type IntTerm[T] = Term[T,Int]
  type IntTerm1[T1] = Term1[T1,Int]
  type IntTerm2[T1,T2] = Term2[T1,T2,Int]
  type IntTerm3[T1,T2,T3] = Term3[T1,T2,T3,Int]
  type IntTerm4[T1,T2,T3,T4] = Term4[T1,T2,T3,T4,Int]
  type IntTerm5[T1,T2,T3,T4,T5] = Term5[T1,T2,T3,T4,T5,Int]
  type IntTerm6[T1,T2,T3,T4,T5,T6] = Term6[T1,T2,T3,T4,T5,T6,Int]
  type IntTerm7[T1,T2,T3,T4,T5,T6,T7] = Term7[T1,T2,T3,T4,T5,T6,T7,Int]
  type IntTerm8[T1,T2,T3,T4,T5,T6,T7,T8] = Term8[T1,T2,T3,T4,T5,T6,T7,T8,Int]
  type IntTerm9[T1,T2,T3,T4,T5,T6,T7,T8,T9] = Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,Int]
  
  trait Term1[T1,R] extends Term[(T1),R] with Function1[T1,R] {
    val convertingFunction = converterOf(this).exprSeq2scala1[T1] _
    type t2c = (Term1[T1,R]) => Term1[T1,Boolean]
    val scalaFunction : (T1) => R
    lazy val evaluator : (Seq[Expr]) => R = (s : Seq[Expr]) => scalaFunction(converter.expr2scala(s(0)).asInstanceOf[T1])
  
    override def apply(x_0 : T1) : R = scalaFunction(x_0)
  
    def ||(other : Term1[T1,Boolean])(implicit asBoolean : (R) => Boolean) : Term1[T1,Boolean] = 
      Term1(this.program, Or(this.expr, other.expr), if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1) => this.scalaFunction(x_0) || other.scalaFunction(x_0), this.types, this.converter)
  
    def &&(other : Term1[T1,Boolean])(implicit asBoolean : (R) => Boolean) : Term1[T1,Boolean] = 
      Term1(this.program, And(this.expr, other.expr), if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1) => this.scalaFunction(x_0) && other.scalaFunction(x_0), this.types, this.converter)
  
    def unary_!(implicit asBoolean : (R) => Boolean) : Term1[T1,Boolean] = 
      Term1(this.program, Not(this.expr), if (this.scalaFunction == null) null else (x_0 : T1) => ! this.scalaFunction(x_0), this.types, this.converter)
  
    def minimizing(minFunc : Term1[T1,Int])(implicit asConstraint : t2c) : MinConstraint1[T1] = {
      MinConstraint1[T1](asConstraint(this), minFunc)
    }
  
    def lazySolve(implicit asConstraint: (Term1[T1,R]) => Constraint1[T1]): (L[T1]) = {
      val constraint = asConstraint(this)
      val (constants, guards) = constantsAndGuards(constraint)
      (createL[T1](constraint, constants(0), guards(0)))
    }

    def lazyFindAll(implicit asConstraint: (Term1[T1,R]) => Constraint1[T1]): LIterator1[T1] = {
      new LIterator1((l: L[T1]) => asConstraint(this))
    }
  
    def compose0[A1](other : Term1[A1, T1]) : Term1[A1, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 1, 1)
      Term1(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1) => this.scalaFunction(other.scalaFunction(x_0)), newTypes, this.converter)
    }
    
    def compose0[A1, A2](other : Term2[A1, A2, T1]) : Term2[A1, A2, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 2, 1)
      Term2(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2) => this.scalaFunction(other.scalaFunction(x_0, x_1)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3](other : Term3[A1, A2, A3, T1]) : Term3[A1, A2, A3, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 3, 1)
      Term3(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3, A4](other : Term4[A1, A2, A3, A4, T1]) : Term4[A1, A2, A3, A4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 4, 1)
      Term4(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : A4) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2, x_3)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3, A4, A5](other : Term5[A1, A2, A3, A4, A5, T1]) : Term5[A1, A2, A3, A4, A5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 5, 1)
      Term5(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : A4, x_4 : A5) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2, x_3, x_4)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3, A4, A5, A6](other : Term6[A1, A2, A3, A4, A5, A6, T1]) : Term6[A1, A2, A3, A4, A5, A6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 6, 1)
      Term6(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : A4, x_4 : A5, x_5 : A6) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3, A4, A5, A6, A7](other : Term7[A1, A2, A3, A4, A5, A6, A7, T1]) : Term7[A1, A2, A3, A4, A5, A6, A7, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 7, 1)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : A4, x_4 : A5, x_5 : A6, x_6 : A7) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5, x_6)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3, A4, A5, A6, A7, A8](other : Term8[A1, A2, A3, A4, A5, A6, A7, A8, T1]) : Term8[A1, A2, A3, A4, A5, A6, A7, A8, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 8, 1)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : A4, x_4 : A5, x_5 : A6, x_6 : A7, x_7 : A8) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3, A4, A5, A6, A7, A8, A9](other : Term9[A1, A2, A3, A4, A5, A6, A7, A8, A9, T1]) : Term9[A1, A2, A3, A4, A5, A6, A7, A8, A9, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 9, 1)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : A4, x_4 : A5, x_5 : A6, x_6 : A7, x_7 : A8, x_8 : A9) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8)), newTypes, this.converter)
    }
  }
  
  trait Term2[T1,T2,R] extends Term[(T1,T2),R] with Function2[T1,T2,R] {
    val convertingFunction = converterOf(this).exprSeq2scala2[T1,T2] _
    type t2c = (Term2[T1,T2,R]) => Term2[T1,T2,Boolean]
    val scalaFunction : (T1,T2) => R
    lazy val evaluator : (Seq[Expr]) => R = (s : Seq[Expr]) => scalaFunction(converter.expr2scala(s(0)).asInstanceOf[T1],converter.expr2scala(s(1)).asInstanceOf[T2])
  
    override def apply(x_0 : T1, x_1 : T2) : R = scalaFunction(x_0, x_1)
  
    def ||(other : Term2[T1,T2,Boolean])(implicit asBoolean : (R) => Boolean) : Term2[T1,T2,Boolean] = 
      Term2(this.program, Or(this.expr, other.expr), if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1,x_1 : T2) => this.scalaFunction(x_0,x_1) || other.scalaFunction(x_0,x_1), this.types, this.converter)
  
    def &&(other : Term2[T1,T2,Boolean])(implicit asBoolean : (R) => Boolean) : Term2[T1,T2,Boolean] = 
      Term2(this.program, And(this.expr, other.expr), if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1,x_1 : T2) => this.scalaFunction(x_0,x_1) && other.scalaFunction(x_0,x_1), this.types, this.converter)
  
    def unary_!(implicit asBoolean : (R) => Boolean) : Term2[T1,T2,Boolean] = 
      Term2(this.program, Not(this.expr), if (this.scalaFunction == null) null else (x_0 : T1,x_1 : T2) => ! this.scalaFunction(x_0,x_1), this.types, this.converter)
  
    def minimizing(minFunc : Term2[T1,T2,Int])(implicit asConstraint : t2c) : MinConstraint2[T1,T2] = {
      MinConstraint2[T1,T2](asConstraint(this), minFunc)
    }
  
    def lazySolve(implicit asConstraint: (Term2[T1,T2,R]) => Constraint2[T1,T2]): (L[T1],L[T2]) = {
      val constraint = asConstraint(this)
      val (constants, guards) = constantsAndGuards(constraint)
      (createL[T1](constraint, constants(0), guards(0)),createL[T2](constraint, constants(1), guards(1)))
    }
  
    def compose0[A1](other : Term1[A1, T1]) : Term2[A1, T2, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 1, 2)
      Term2(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : T2) => this.scalaFunction(other.scalaFunction(x_0), x_1), newTypes, this.converter)
    }
    
    def compose1[A1](other : Term1[A1, T2]) : Term2[T1, A1, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 1, 2)
      Term2(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1) => this.scalaFunction(x_0, other.scalaFunction(x_1)), newTypes, this.converter)
    }
    
    def compose0[A1, A2](other : Term2[A1, A2, T1]) : Term3[A1, A2, T2, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 2, 2)
      Term3(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : T2) => this.scalaFunction(other.scalaFunction(x_0, x_1), x_2), newTypes, this.converter)
    }
    
    def compose1[A1, A2](other : Term2[A1, A2, T2]) : Term3[T1, A1, A2, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 2, 2)
      Term3(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3](other : Term3[A1, A2, A3, T1]) : Term4[A1, A2, A3, T2, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 3, 2)
      Term4(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : T2) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2), x_3), newTypes, this.converter)
    }
    
    def compose1[A1, A2, A3](other : Term3[A1, A2, A3, T2]) : Term4[T1, A1, A2, A3, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 3, 2)
      Term4(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : A3) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2, x_3)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3, A4](other : Term4[A1, A2, A3, A4, T1]) : Term5[A1, A2, A3, A4, T2, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 4, 2)
      Term5(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : A4, x_4 : T2) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2, x_3), x_4), newTypes, this.converter)
    }
    
    def compose1[A1, A2, A3, A4](other : Term4[A1, A2, A3, A4, T2]) : Term5[T1, A1, A2, A3, A4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 4, 2)
      Term5(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : A3, x_4 : A4) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2, x_3, x_4)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3, A4, A5](other : Term5[A1, A2, A3, A4, A5, T1]) : Term6[A1, A2, A3, A4, A5, T2, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 5, 2)
      Term6(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : A4, x_4 : A5, x_5 : T2) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2, x_3, x_4), x_5), newTypes, this.converter)
    }
    
    def compose1[A1, A2, A3, A4, A5](other : Term5[A1, A2, A3, A4, A5, T2]) : Term6[T1, A1, A2, A3, A4, A5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 5, 2)
      Term6(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : A3, x_4 : A4, x_5 : A5) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2, x_3, x_4, x_5)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3, A4, A5, A6](other : Term6[A1, A2, A3, A4, A5, A6, T1]) : Term7[A1, A2, A3, A4, A5, A6, T2, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 6, 2)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : A4, x_4 : A5, x_5 : A6, x_6 : T2) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5), x_6), newTypes, this.converter)
    }
    
    def compose1[A1, A2, A3, A4, A5, A6](other : Term6[A1, A2, A3, A4, A5, A6, T2]) : Term7[T1, A1, A2, A3, A4, A5, A6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 6, 2)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : A3, x_4 : A4, x_5 : A5, x_6 : A6) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2, x_3, x_4, x_5, x_6)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3, A4, A5, A6, A7](other : Term7[A1, A2, A3, A4, A5, A6, A7, T1]) : Term8[A1, A2, A3, A4, A5, A6, A7, T2, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 7, 2)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : A4, x_4 : A5, x_5 : A6, x_6 : A7, x_7 : T2) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5, x_6), x_7), newTypes, this.converter)
    }
    
    def compose1[A1, A2, A3, A4, A5, A6, A7](other : Term7[A1, A2, A3, A4, A5, A6, A7, T2]) : Term8[T1, A1, A2, A3, A4, A5, A6, A7, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 7, 2)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : A3, x_4 : A4, x_5 : A5, x_6 : A6, x_7 : A7) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2, x_3, x_4, x_5, x_6, x_7)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3, A4, A5, A6, A7, A8](other : Term8[A1, A2, A3, A4, A5, A6, A7, A8, T1]) : Term9[A1, A2, A3, A4, A5, A6, A7, A8, T2, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 8, 2)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : A4, x_4 : A5, x_5 : A6, x_6 : A7, x_7 : A8, x_8 : T2) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7), x_8), newTypes, this.converter)
    }
    
    def compose1[A1, A2, A3, A4, A5, A6, A7, A8](other : Term8[A1, A2, A3, A4, A5, A6, A7, A8, T2]) : Term9[T1, A1, A2, A3, A4, A5, A6, A7, A8, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 8, 2)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : A3, x_4 : A4, x_5 : A5, x_6 : A6, x_7 : A7, x_8 : A8) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8)), newTypes, this.converter)
    }
  }
  
  trait Term3[T1,T2,T3,R] extends Term[(T1,T2,T3),R] with Function3[T1,T2,T3,R] {
    val convertingFunction = converterOf(this).exprSeq2scala3[T1,T2,T3] _
    type t2c = (Term3[T1,T2,T3,R]) => Term3[T1,T2,T3,Boolean]
    val scalaFunction : (T1,T2,T3) => R
    lazy val evaluator : (Seq[Expr]) => R = (s : Seq[Expr]) => scalaFunction(converter.expr2scala(s(0)).asInstanceOf[T1],converter.expr2scala(s(1)).asInstanceOf[T2],converter.expr2scala(s(2)).asInstanceOf[T3])
  
    override def apply(x_0 : T1, x_1 : T2, x_2 : T3) : R = scalaFunction(x_0, x_1, x_2)
  
    def ||(other : Term3[T1,T2,T3,Boolean])(implicit asBoolean : (R) => Boolean) : Term3[T1,T2,T3,Boolean] = 
      Term3(this.program, Or(this.expr, other.expr), if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1,x_1 : T2,x_2 : T3) => this.scalaFunction(x_0,x_1,x_2) || other.scalaFunction(x_0,x_1,x_2), this.types, this.converter)
  
    def &&(other : Term3[T1,T2,T3,Boolean])(implicit asBoolean : (R) => Boolean) : Term3[T1,T2,T3,Boolean] = 
      Term3(this.program, And(this.expr, other.expr), if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1,x_1 : T2,x_2 : T3) => this.scalaFunction(x_0,x_1,x_2) && other.scalaFunction(x_0,x_1,x_2), this.types, this.converter)
  
    def unary_!(implicit asBoolean : (R) => Boolean) : Term3[T1,T2,T3,Boolean] = 
      Term3(this.program, Not(this.expr), if (this.scalaFunction == null) null else (x_0 : T1,x_1 : T2,x_2 : T3) => ! this.scalaFunction(x_0,x_1,x_2), this.types, this.converter)
  
    def minimizing(minFunc : Term3[T1,T2,T3,Int])(implicit asConstraint : t2c) : MinConstraint3[T1,T2,T3] = {
      MinConstraint3[T1,T2,T3](asConstraint(this), minFunc)
    }
  
    def lazySolve(implicit asConstraint: (Term3[T1,T2,T3,R]) => Constraint3[T1,T2,T3]): (L[T1],L[T2],L[T3]) = {
      val constraint = asConstraint(this)
      val (constants, guards) = constantsAndGuards(constraint)
      (createL[T1](constraint, constants(0), guards(0)),createL[T2](constraint, constants(1), guards(1)),createL[T3](constraint, constants(2), guards(2)))
    }
  
    def compose0[A1](other : Term1[A1, T1]) : Term3[A1, T2, T3, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 1, 3)
      Term3(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : T2, x_2 : T3) => this.scalaFunction(other.scalaFunction(x_0), x_1, x_2), newTypes, this.converter)
    }
    
    def compose1[A1](other : Term1[A1, T2]) : Term3[T1, A1, T3, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 1, 3)
      Term3(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : T3) => this.scalaFunction(x_0, other.scalaFunction(x_1), x_2), newTypes, this.converter)
    }
    
    def compose2[A1](other : Term1[A1, T3]) : Term3[T1, T2, A1, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 1, 3)
      Term3(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2)), newTypes, this.converter)
    }
    
    def compose0[A1, A2](other : Term2[A1, A2, T1]) : Term4[A1, A2, T2, T3, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 2, 3)
      Term4(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : T2, x_3 : T3) => this.scalaFunction(other.scalaFunction(x_0, x_1), x_2, x_3), newTypes, this.converter)
    }
    
    def compose1[A1, A2](other : Term2[A1, A2, T2]) : Term4[T1, A1, A2, T3, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 2, 3)
      Term4(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : T3) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2), x_3), newTypes, this.converter)
    }
    
    def compose2[A1, A2](other : Term2[A1, A2, T3]) : Term4[T1, T2, A1, A2, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 2, 3)
      Term4(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : A2) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2, x_3)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3](other : Term3[A1, A2, A3, T1]) : Term5[A1, A2, A3, T2, T3, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 3, 3)
      Term5(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : T2, x_4 : T3) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2), x_3, x_4), newTypes, this.converter)
    }
    
    def compose1[A1, A2, A3](other : Term3[A1, A2, A3, T2]) : Term5[T1, A1, A2, A3, T3, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 3, 3)
      Term5(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : A3, x_4 : T3) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2, x_3), x_4), newTypes, this.converter)
    }
    
    def compose2[A1, A2, A3](other : Term3[A1, A2, A3, T3]) : Term5[T1, T2, A1, A2, A3, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 3, 3)
      Term5(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : A2, x_4 : A3) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2, x_3, x_4)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3, A4](other : Term4[A1, A2, A3, A4, T1]) : Term6[A1, A2, A3, A4, T2, T3, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 4, 3)
      Term6(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : A4, x_4 : T2, x_5 : T3) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2, x_3), x_4, x_5), newTypes, this.converter)
    }
    
    def compose1[A1, A2, A3, A4](other : Term4[A1, A2, A3, A4, T2]) : Term6[T1, A1, A2, A3, A4, T3, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 4, 3)
      Term6(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : A3, x_4 : A4, x_5 : T3) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2, x_3, x_4), x_5), newTypes, this.converter)
    }
    
    def compose2[A1, A2, A3, A4](other : Term4[A1, A2, A3, A4, T3]) : Term6[T1, T2, A1, A2, A3, A4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 4, 3)
      Term6(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : A2, x_4 : A3, x_5 : A4) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2, x_3, x_4, x_5)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3, A4, A5](other : Term5[A1, A2, A3, A4, A5, T1]) : Term7[A1, A2, A3, A4, A5, T2, T3, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 5, 3)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : A4, x_4 : A5, x_5 : T2, x_6 : T3) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2, x_3, x_4), x_5, x_6), newTypes, this.converter)
    }
    
    def compose1[A1, A2, A3, A4, A5](other : Term5[A1, A2, A3, A4, A5, T2]) : Term7[T1, A1, A2, A3, A4, A5, T3, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 5, 3)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : A3, x_4 : A4, x_5 : A5, x_6 : T3) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2, x_3, x_4, x_5), x_6), newTypes, this.converter)
    }
    
    def compose2[A1, A2, A3, A4, A5](other : Term5[A1, A2, A3, A4, A5, T3]) : Term7[T1, T2, A1, A2, A3, A4, A5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 5, 3)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : A2, x_4 : A3, x_5 : A4, x_6 : A5) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2, x_3, x_4, x_5, x_6)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3, A4, A5, A6](other : Term6[A1, A2, A3, A4, A5, A6, T1]) : Term8[A1, A2, A3, A4, A5, A6, T2, T3, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 6, 3)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : A4, x_4 : A5, x_5 : A6, x_6 : T2, x_7 : T3) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5), x_6, x_7), newTypes, this.converter)
    }
    
    def compose1[A1, A2, A3, A4, A5, A6](other : Term6[A1, A2, A3, A4, A5, A6, T2]) : Term8[T1, A1, A2, A3, A4, A5, A6, T3, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 6, 3)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : A3, x_4 : A4, x_5 : A5, x_6 : A6, x_7 : T3) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2, x_3, x_4, x_5, x_6), x_7), newTypes, this.converter)
    }
    
    def compose2[A1, A2, A3, A4, A5, A6](other : Term6[A1, A2, A3, A4, A5, A6, T3]) : Term8[T1, T2, A1, A2, A3, A4, A5, A6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 6, 3)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : A2, x_4 : A3, x_5 : A4, x_6 : A5, x_7 : A6) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2, x_3, x_4, x_5, x_6, x_7)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3, A4, A5, A6, A7](other : Term7[A1, A2, A3, A4, A5, A6, A7, T1]) : Term9[A1, A2, A3, A4, A5, A6, A7, T2, T3, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 7, 3)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : A4, x_4 : A5, x_5 : A6, x_6 : A7, x_7 : T2, x_8 : T3) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5, x_6), x_7, x_8), newTypes, this.converter)
    }
    
    def compose1[A1, A2, A3, A4, A5, A6, A7](other : Term7[A1, A2, A3, A4, A5, A6, A7, T2]) : Term9[T1, A1, A2, A3, A4, A5, A6, A7, T3, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 7, 3)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : A3, x_4 : A4, x_5 : A5, x_6 : A6, x_7 : A7, x_8 : T3) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2, x_3, x_4, x_5, x_6, x_7), x_8), newTypes, this.converter)
    }
    
    def compose2[A1, A2, A3, A4, A5, A6, A7](other : Term7[A1, A2, A3, A4, A5, A6, A7, T3]) : Term9[T1, T2, A1, A2, A3, A4, A5, A6, A7, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 7, 3)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : A2, x_4 : A3, x_5 : A4, x_6 : A5, x_7 : A6, x_8 : A7) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2, x_3, x_4, x_5, x_6, x_7, x_8)), newTypes, this.converter)
    }
  }
  
  trait Term4[T1,T2,T3,T4,R] extends Term[(T1,T2,T3,T4),R] with Function4[T1,T2,T3,T4,R] {
    val convertingFunction = converterOf(this).exprSeq2scala4[T1,T2,T3,T4] _
    type t2c = (Term4[T1,T2,T3,T4,R]) => Term4[T1,T2,T3,T4,Boolean]
    val scalaFunction : (T1,T2,T3,T4) => R
    lazy val evaluator : (Seq[Expr]) => R = (s : Seq[Expr]) => scalaFunction(converter.expr2scala(s(0)).asInstanceOf[T1],converter.expr2scala(s(1)).asInstanceOf[T2],converter.expr2scala(s(2)).asInstanceOf[T3],converter.expr2scala(s(3)).asInstanceOf[T4])
  
    override def apply(x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4) : R = scalaFunction(x_0, x_1, x_2, x_3)
  
    def ||(other : Term4[T1,T2,T3,T4,Boolean])(implicit asBoolean : (R) => Boolean) : Term4[T1,T2,T3,T4,Boolean] = 
      Term4(this.program, Or(this.expr, other.expr), if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1,x_1 : T2,x_2 : T3,x_3 : T4) => this.scalaFunction(x_0,x_1,x_2,x_3) || other.scalaFunction(x_0,x_1,x_2,x_3), this.types, this.converter)
  
    def &&(other : Term4[T1,T2,T3,T4,Boolean])(implicit asBoolean : (R) => Boolean) : Term4[T1,T2,T3,T4,Boolean] = 
      Term4(this.program, And(this.expr, other.expr), if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1,x_1 : T2,x_2 : T3,x_3 : T4) => this.scalaFunction(x_0,x_1,x_2,x_3) && other.scalaFunction(x_0,x_1,x_2,x_3), this.types, this.converter)
  
    def unary_!(implicit asBoolean : (R) => Boolean) : Term4[T1,T2,T3,T4,Boolean] = 
      Term4(this.program, Not(this.expr), if (this.scalaFunction == null) null else (x_0 : T1,x_1 : T2,x_2 : T3,x_3 : T4) => ! this.scalaFunction(x_0,x_1,x_2,x_3), this.types, this.converter)
  
    def minimizing(minFunc : Term4[T1,T2,T3,T4,Int])(implicit asConstraint : t2c) : MinConstraint4[T1,T2,T3,T4] = {
      MinConstraint4[T1,T2,T3,T4](asConstraint(this), minFunc)
    }
  
    def lazySolve(implicit asConstraint: (Term4[T1,T2,T3,T4,R]) => Constraint4[T1,T2,T3,T4]): (L[T1],L[T2],L[T3],L[T4]) = {
      val constraint = asConstraint(this)
      val (constants, guards) = constantsAndGuards(constraint)
      (createL[T1](constraint, constants(0), guards(0)),createL[T2](constraint, constants(1), guards(1)),createL[T3](constraint, constants(2), guards(2)),createL[T4](constraint, constants(3), guards(3)))
    }
  
    def compose0[A1](other : Term1[A1, T1]) : Term4[A1, T2, T3, T4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 1, 4)
      Term4(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : T2, x_2 : T3, x_3 : T4) => this.scalaFunction(other.scalaFunction(x_0), x_1, x_2, x_3), newTypes, this.converter)
    }
    
    def compose1[A1](other : Term1[A1, T2]) : Term4[T1, A1, T3, T4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 1, 4)
      Term4(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : T3, x_3 : T4) => this.scalaFunction(x_0, other.scalaFunction(x_1), x_2, x_3), newTypes, this.converter)
    }
    
    def compose2[A1](other : Term1[A1, T3]) : Term4[T1, T2, A1, T4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 1, 4)
      Term4(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : T4) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2), x_3), newTypes, this.converter)
    }
    
    def compose3[A1](other : Term1[A1, T4]) : Term4[T1, T2, T3, A1, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 3, 1, 4)
      Term4(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : A1) => this.scalaFunction(x_0, x_1, x_2, other.scalaFunction(x_3)), newTypes, this.converter)
    }
    
    def compose0[A1, A2](other : Term2[A1, A2, T1]) : Term5[A1, A2, T2, T3, T4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 2, 4)
      Term5(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : T2, x_3 : T3, x_4 : T4) => this.scalaFunction(other.scalaFunction(x_0, x_1), x_2, x_3, x_4), newTypes, this.converter)
    }
    
    def compose1[A1, A2](other : Term2[A1, A2, T2]) : Term5[T1, A1, A2, T3, T4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 2, 4)
      Term5(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : T3, x_4 : T4) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2), x_3, x_4), newTypes, this.converter)
    }
    
    def compose2[A1, A2](other : Term2[A1, A2, T3]) : Term5[T1, T2, A1, A2, T4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 2, 4)
      Term5(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : A2, x_4 : T4) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2, x_3), x_4), newTypes, this.converter)
    }
    
    def compose3[A1, A2](other : Term2[A1, A2, T4]) : Term5[T1, T2, T3, A1, A2, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 3, 2, 4)
      Term5(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : A1, x_4 : A2) => this.scalaFunction(x_0, x_1, x_2, other.scalaFunction(x_3, x_4)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3](other : Term3[A1, A2, A3, T1]) : Term6[A1, A2, A3, T2, T3, T4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 3, 4)
      Term6(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : T2, x_4 : T3, x_5 : T4) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2), x_3, x_4, x_5), newTypes, this.converter)
    }
    
    def compose1[A1, A2, A3](other : Term3[A1, A2, A3, T2]) : Term6[T1, A1, A2, A3, T3, T4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 3, 4)
      Term6(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : A3, x_4 : T3, x_5 : T4) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2, x_3), x_4, x_5), newTypes, this.converter)
    }
    
    def compose2[A1, A2, A3](other : Term3[A1, A2, A3, T3]) : Term6[T1, T2, A1, A2, A3, T4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 3, 4)
      Term6(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : A2, x_4 : A3, x_5 : T4) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2, x_3, x_4), x_5), newTypes, this.converter)
    }
    
    def compose3[A1, A2, A3](other : Term3[A1, A2, A3, T4]) : Term6[T1, T2, T3, A1, A2, A3, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 3, 3, 4)
      Term6(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : A1, x_4 : A2, x_5 : A3) => this.scalaFunction(x_0, x_1, x_2, other.scalaFunction(x_3, x_4, x_5)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3, A4](other : Term4[A1, A2, A3, A4, T1]) : Term7[A1, A2, A3, A4, T2, T3, T4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 4, 4)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : A4, x_4 : T2, x_5 : T3, x_6 : T4) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2, x_3), x_4, x_5, x_6), newTypes, this.converter)
    }
    
    def compose1[A1, A2, A3, A4](other : Term4[A1, A2, A3, A4, T2]) : Term7[T1, A1, A2, A3, A4, T3, T4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 4, 4)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : A3, x_4 : A4, x_5 : T3, x_6 : T4) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2, x_3, x_4), x_5, x_6), newTypes, this.converter)
    }
    
    def compose2[A1, A2, A3, A4](other : Term4[A1, A2, A3, A4, T3]) : Term7[T1, T2, A1, A2, A3, A4, T4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 4, 4)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : A2, x_4 : A3, x_5 : A4, x_6 : T4) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2, x_3, x_4, x_5), x_6), newTypes, this.converter)
    }
    
    def compose3[A1, A2, A3, A4](other : Term4[A1, A2, A3, A4, T4]) : Term7[T1, T2, T3, A1, A2, A3, A4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 3, 4, 4)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : A1, x_4 : A2, x_5 : A3, x_6 : A4) => this.scalaFunction(x_0, x_1, x_2, other.scalaFunction(x_3, x_4, x_5, x_6)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3, A4, A5](other : Term5[A1, A2, A3, A4, A5, T1]) : Term8[A1, A2, A3, A4, A5, T2, T3, T4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 5, 4)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : A4, x_4 : A5, x_5 : T2, x_6 : T3, x_7 : T4) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2, x_3, x_4), x_5, x_6, x_7), newTypes, this.converter)
    }
    
    def compose1[A1, A2, A3, A4, A5](other : Term5[A1, A2, A3, A4, A5, T2]) : Term8[T1, A1, A2, A3, A4, A5, T3, T4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 5, 4)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : A3, x_4 : A4, x_5 : A5, x_6 : T3, x_7 : T4) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2, x_3, x_4, x_5), x_6, x_7), newTypes, this.converter)
    }
    
    def compose2[A1, A2, A3, A4, A5](other : Term5[A1, A2, A3, A4, A5, T3]) : Term8[T1, T2, A1, A2, A3, A4, A5, T4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 5, 4)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : A2, x_4 : A3, x_5 : A4, x_6 : A5, x_7 : T4) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2, x_3, x_4, x_5, x_6), x_7), newTypes, this.converter)
    }
    
    def compose3[A1, A2, A3, A4, A5](other : Term5[A1, A2, A3, A4, A5, T4]) : Term8[T1, T2, T3, A1, A2, A3, A4, A5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 3, 5, 4)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : A1, x_4 : A2, x_5 : A3, x_6 : A4, x_7 : A5) => this.scalaFunction(x_0, x_1, x_2, other.scalaFunction(x_3, x_4, x_5, x_6, x_7)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3, A4, A5, A6](other : Term6[A1, A2, A3, A4, A5, A6, T1]) : Term9[A1, A2, A3, A4, A5, A6, T2, T3, T4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 6, 4)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : A4, x_4 : A5, x_5 : A6, x_6 : T2, x_7 : T3, x_8 : T4) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5), x_6, x_7, x_8), newTypes, this.converter)
    }
    
    def compose1[A1, A2, A3, A4, A5, A6](other : Term6[A1, A2, A3, A4, A5, A6, T2]) : Term9[T1, A1, A2, A3, A4, A5, A6, T3, T4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 6, 4)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : A3, x_4 : A4, x_5 : A5, x_6 : A6, x_7 : T3, x_8 : T4) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2, x_3, x_4, x_5, x_6), x_7, x_8), newTypes, this.converter)
    }
    
    def compose2[A1, A2, A3, A4, A5, A6](other : Term6[A1, A2, A3, A4, A5, A6, T3]) : Term9[T1, T2, A1, A2, A3, A4, A5, A6, T4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 6, 4)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : A2, x_4 : A3, x_5 : A4, x_6 : A5, x_7 : A6, x_8 : T4) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2, x_3, x_4, x_5, x_6, x_7), x_8), newTypes, this.converter)
    }
    
    def compose3[A1, A2, A3, A4, A5, A6](other : Term6[A1, A2, A3, A4, A5, A6, T4]) : Term9[T1, T2, T3, A1, A2, A3, A4, A5, A6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 3, 6, 4)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : A1, x_4 : A2, x_5 : A3, x_6 : A4, x_7 : A5, x_8 : A6) => this.scalaFunction(x_0, x_1, x_2, other.scalaFunction(x_3, x_4, x_5, x_6, x_7, x_8)), newTypes, this.converter)
    }
  }
  
  trait Term5[T1,T2,T3,T4,T5,R] extends Term[(T1,T2,T3,T4,T5),R] with Function5[T1,T2,T3,T4,T5,R] {
    val convertingFunction = converterOf(this).exprSeq2scala5[T1,T2,T3,T4,T5] _
    type t2c = (Term5[T1,T2,T3,T4,T5,R]) => Term5[T1,T2,T3,T4,T5,Boolean]
    val scalaFunction : (T1,T2,T3,T4,T5) => R
    lazy val evaluator : (Seq[Expr]) => R = (s : Seq[Expr]) => scalaFunction(converter.expr2scala(s(0)).asInstanceOf[T1],converter.expr2scala(s(1)).asInstanceOf[T2],converter.expr2scala(s(2)).asInstanceOf[T3],converter.expr2scala(s(3)).asInstanceOf[T4],converter.expr2scala(s(4)).asInstanceOf[T5])
  
    override def apply(x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5) : R = scalaFunction(x_0, x_1, x_2, x_3, x_4)
  
    def ||(other : Term5[T1,T2,T3,T4,T5,Boolean])(implicit asBoolean : (R) => Boolean) : Term5[T1,T2,T3,T4,T5,Boolean] = 
      Term5(this.program, Or(this.expr, other.expr), if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1,x_1 : T2,x_2 : T3,x_3 : T4,x_4 : T5) => this.scalaFunction(x_0,x_1,x_2,x_3,x_4) || other.scalaFunction(x_0,x_1,x_2,x_3,x_4), this.types, this.converter)
  
    def &&(other : Term5[T1,T2,T3,T4,T5,Boolean])(implicit asBoolean : (R) => Boolean) : Term5[T1,T2,T3,T4,T5,Boolean] = 
      Term5(this.program, And(this.expr, other.expr), if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1,x_1 : T2,x_2 : T3,x_3 : T4,x_4 : T5) => this.scalaFunction(x_0,x_1,x_2,x_3,x_4) && other.scalaFunction(x_0,x_1,x_2,x_3,x_4), this.types, this.converter)
  
    def unary_!(implicit asBoolean : (R) => Boolean) : Term5[T1,T2,T3,T4,T5,Boolean] = 
      Term5(this.program, Not(this.expr), if (this.scalaFunction == null) null else (x_0 : T1,x_1 : T2,x_2 : T3,x_3 : T4,x_4 : T5) => ! this.scalaFunction(x_0,x_1,x_2,x_3,x_4), this.types, this.converter)
  
    def minimizing(minFunc : Term5[T1,T2,T3,T4,T5,Int])(implicit asConstraint : t2c) : MinConstraint5[T1,T2,T3,T4,T5] = {
      MinConstraint5[T1,T2,T3,T4,T5](asConstraint(this), minFunc)
    }
  
    def lazySolve(implicit asConstraint: (Term5[T1,T2,T3,T4,T5,R]) => Constraint5[T1,T2,T3,T4,T5]): (L[T1],L[T2],L[T3],L[T4],L[T5]) = {
      val constraint = asConstraint(this)
      val (constants, guards) = constantsAndGuards(constraint)
      (createL[T1](constraint, constants(0), guards(0)),createL[T2](constraint, constants(1), guards(1)),createL[T3](constraint, constants(2), guards(2)),createL[T4](constraint, constants(3), guards(3)),createL[T5](constraint, constants(4), guards(4)))
    }
  
    def compose0[A1](other : Term1[A1, T1]) : Term5[A1, T2, T3, T4, T5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 1, 5)
      Term5(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5) => this.scalaFunction(other.scalaFunction(x_0), x_1, x_2, x_3, x_4), newTypes, this.converter)
    }
    
    def compose1[A1](other : Term1[A1, T2]) : Term5[T1, A1, T3, T4, T5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 1, 5)
      Term5(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : T3, x_3 : T4, x_4 : T5) => this.scalaFunction(x_0, other.scalaFunction(x_1), x_2, x_3, x_4), newTypes, this.converter)
    }
    
    def compose2[A1](other : Term1[A1, T3]) : Term5[T1, T2, A1, T4, T5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 1, 5)
      Term5(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : T4, x_4 : T5) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2), x_3, x_4), newTypes, this.converter)
    }
    
    def compose3[A1](other : Term1[A1, T4]) : Term5[T1, T2, T3, A1, T5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 3, 1, 5)
      Term5(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : A1, x_4 : T5) => this.scalaFunction(x_0, x_1, x_2, other.scalaFunction(x_3), x_4), newTypes, this.converter)
    }
    
    def compose4[A1](other : Term1[A1, T5]) : Term5[T1, T2, T3, T4, A1, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 4, 1, 5)
      Term5(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : A1) => this.scalaFunction(x_0, x_1, x_2, x_3, other.scalaFunction(x_4)), newTypes, this.converter)
    }
    
    def compose0[A1, A2](other : Term2[A1, A2, T1]) : Term6[A1, A2, T2, T3, T4, T5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 2, 5)
      Term6(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : T2, x_3 : T3, x_4 : T4, x_5 : T5) => this.scalaFunction(other.scalaFunction(x_0, x_1), x_2, x_3, x_4, x_5), newTypes, this.converter)
    }
    
    def compose1[A1, A2](other : Term2[A1, A2, T2]) : Term6[T1, A1, A2, T3, T4, T5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 2, 5)
      Term6(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : T3, x_4 : T4, x_5 : T5) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2), x_3, x_4, x_5), newTypes, this.converter)
    }
    
    def compose2[A1, A2](other : Term2[A1, A2, T3]) : Term6[T1, T2, A1, A2, T4, T5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 2, 5)
      Term6(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : A2, x_4 : T4, x_5 : T5) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2, x_3), x_4, x_5), newTypes, this.converter)
    }
    
    def compose3[A1, A2](other : Term2[A1, A2, T4]) : Term6[T1, T2, T3, A1, A2, T5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 3, 2, 5)
      Term6(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : A1, x_4 : A2, x_5 : T5) => this.scalaFunction(x_0, x_1, x_2, other.scalaFunction(x_3, x_4), x_5), newTypes, this.converter)
    }
    
    def compose4[A1, A2](other : Term2[A1, A2, T5]) : Term6[T1, T2, T3, T4, A1, A2, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 4, 2, 5)
      Term6(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : A1, x_5 : A2) => this.scalaFunction(x_0, x_1, x_2, x_3, other.scalaFunction(x_4, x_5)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3](other : Term3[A1, A2, A3, T1]) : Term7[A1, A2, A3, T2, T3, T4, T5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 3, 5)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : T2, x_4 : T3, x_5 : T4, x_6 : T5) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2), x_3, x_4, x_5, x_6), newTypes, this.converter)
    }
    
    def compose1[A1, A2, A3](other : Term3[A1, A2, A3, T2]) : Term7[T1, A1, A2, A3, T3, T4, T5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 3, 5)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : A3, x_4 : T3, x_5 : T4, x_6 : T5) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2, x_3), x_4, x_5, x_6), newTypes, this.converter)
    }
    
    def compose2[A1, A2, A3](other : Term3[A1, A2, A3, T3]) : Term7[T1, T2, A1, A2, A3, T4, T5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 3, 5)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : A2, x_4 : A3, x_5 : T4, x_6 : T5) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2, x_3, x_4), x_5, x_6), newTypes, this.converter)
    }
    
    def compose3[A1, A2, A3](other : Term3[A1, A2, A3, T4]) : Term7[T1, T2, T3, A1, A2, A3, T5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 3, 3, 5)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : A1, x_4 : A2, x_5 : A3, x_6 : T5) => this.scalaFunction(x_0, x_1, x_2, other.scalaFunction(x_3, x_4, x_5), x_6), newTypes, this.converter)
    }
    
    def compose4[A1, A2, A3](other : Term3[A1, A2, A3, T5]) : Term7[T1, T2, T3, T4, A1, A2, A3, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 4, 3, 5)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : A1, x_5 : A2, x_6 : A3) => this.scalaFunction(x_0, x_1, x_2, x_3, other.scalaFunction(x_4, x_5, x_6)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3, A4](other : Term4[A1, A2, A3, A4, T1]) : Term8[A1, A2, A3, A4, T2, T3, T4, T5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 4, 5)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : A4, x_4 : T2, x_5 : T3, x_6 : T4, x_7 : T5) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2, x_3), x_4, x_5, x_6, x_7), newTypes, this.converter)
    }
    
    def compose1[A1, A2, A3, A4](other : Term4[A1, A2, A3, A4, T2]) : Term8[T1, A1, A2, A3, A4, T3, T4, T5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 4, 5)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : A3, x_4 : A4, x_5 : T3, x_6 : T4, x_7 : T5) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2, x_3, x_4), x_5, x_6, x_7), newTypes, this.converter)
    }
    
    def compose2[A1, A2, A3, A4](other : Term4[A1, A2, A3, A4, T3]) : Term8[T1, T2, A1, A2, A3, A4, T4, T5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 4, 5)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : A2, x_4 : A3, x_5 : A4, x_6 : T4, x_7 : T5) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2, x_3, x_4, x_5), x_6, x_7), newTypes, this.converter)
    }
    
    def compose3[A1, A2, A3, A4](other : Term4[A1, A2, A3, A4, T4]) : Term8[T1, T2, T3, A1, A2, A3, A4, T5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 3, 4, 5)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : A1, x_4 : A2, x_5 : A3, x_6 : A4, x_7 : T5) => this.scalaFunction(x_0, x_1, x_2, other.scalaFunction(x_3, x_4, x_5, x_6), x_7), newTypes, this.converter)
    }
    
    def compose4[A1, A2, A3, A4](other : Term4[A1, A2, A3, A4, T5]) : Term8[T1, T2, T3, T4, A1, A2, A3, A4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 4, 4, 5)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : A1, x_5 : A2, x_6 : A3, x_7 : A4) => this.scalaFunction(x_0, x_1, x_2, x_3, other.scalaFunction(x_4, x_5, x_6, x_7)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3, A4, A5](other : Term5[A1, A2, A3, A4, A5, T1]) : Term9[A1, A2, A3, A4, A5, T2, T3, T4, T5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 5, 5)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : A4, x_4 : A5, x_5 : T2, x_6 : T3, x_7 : T4, x_8 : T5) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2, x_3, x_4), x_5, x_6, x_7, x_8), newTypes, this.converter)
    }
    
    def compose1[A1, A2, A3, A4, A5](other : Term5[A1, A2, A3, A4, A5, T2]) : Term9[T1, A1, A2, A3, A4, A5, T3, T4, T5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 5, 5)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : A3, x_4 : A4, x_5 : A5, x_6 : T3, x_7 : T4, x_8 : T5) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2, x_3, x_4, x_5), x_6, x_7, x_8), newTypes, this.converter)
    }
    
    def compose2[A1, A2, A3, A4, A5](other : Term5[A1, A2, A3, A4, A5, T3]) : Term9[T1, T2, A1, A2, A3, A4, A5, T4, T5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 5, 5)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : A2, x_4 : A3, x_5 : A4, x_6 : A5, x_7 : T4, x_8 : T5) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2, x_3, x_4, x_5, x_6), x_7, x_8), newTypes, this.converter)
    }
    
    def compose3[A1, A2, A3, A4, A5](other : Term5[A1, A2, A3, A4, A5, T4]) : Term9[T1, T2, T3, A1, A2, A3, A4, A5, T5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 3, 5, 5)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : A1, x_4 : A2, x_5 : A3, x_6 : A4, x_7 : A5, x_8 : T5) => this.scalaFunction(x_0, x_1, x_2, other.scalaFunction(x_3, x_4, x_5, x_6, x_7), x_8), newTypes, this.converter)
    }
    
    def compose4[A1, A2, A3, A4, A5](other : Term5[A1, A2, A3, A4, A5, T5]) : Term9[T1, T2, T3, T4, A1, A2, A3, A4, A5, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 4, 5, 5)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : A1, x_5 : A2, x_6 : A3, x_7 : A4, x_8 : A5) => this.scalaFunction(x_0, x_1, x_2, x_3, other.scalaFunction(x_4, x_5, x_6, x_7, x_8)), newTypes, this.converter)
    }
  }
  
  trait Term6[T1,T2,T3,T4,T5,T6,R] extends Term[(T1,T2,T3,T4,T5,T6),R] with Function6[T1,T2,T3,T4,T5,T6,R] {
    val convertingFunction = converterOf(this).exprSeq2scala6[T1,T2,T3,T4,T5,T6] _
    type t2c = (Term6[T1,T2,T3,T4,T5,T6,R]) => Term6[T1,T2,T3,T4,T5,T6,Boolean]
    val scalaFunction : (T1,T2,T3,T4,T5,T6) => R
    lazy val evaluator : (Seq[Expr]) => R = (s : Seq[Expr]) => scalaFunction(converter.expr2scala(s(0)).asInstanceOf[T1],converter.expr2scala(s(1)).asInstanceOf[T2],converter.expr2scala(s(2)).asInstanceOf[T3],converter.expr2scala(s(3)).asInstanceOf[T4],converter.expr2scala(s(4)).asInstanceOf[T5],converter.expr2scala(s(5)).asInstanceOf[T6])
  
    override def apply(x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : T6) : R = scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5)
  
    def ||(other : Term6[T1,T2,T3,T4,T5,T6,Boolean])(implicit asBoolean : (R) => Boolean) : Term6[T1,T2,T3,T4,T5,T6,Boolean] = 
      Term6(this.program, Or(this.expr, other.expr), if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1,x_1 : T2,x_2 : T3,x_3 : T4,x_4 : T5,x_5 : T6) => this.scalaFunction(x_0,x_1,x_2,x_3,x_4,x_5) || other.scalaFunction(x_0,x_1,x_2,x_3,x_4,x_5), this.types, this.converter)
  
    def &&(other : Term6[T1,T2,T3,T4,T5,T6,Boolean])(implicit asBoolean : (R) => Boolean) : Term6[T1,T2,T3,T4,T5,T6,Boolean] = 
      Term6(this.program, And(this.expr, other.expr), if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1,x_1 : T2,x_2 : T3,x_3 : T4,x_4 : T5,x_5 : T6) => this.scalaFunction(x_0,x_1,x_2,x_3,x_4,x_5) && other.scalaFunction(x_0,x_1,x_2,x_3,x_4,x_5), this.types, this.converter)
  
    def unary_!(implicit asBoolean : (R) => Boolean) : Term6[T1,T2,T3,T4,T5,T6,Boolean] = 
      Term6(this.program, Not(this.expr), if (this.scalaFunction == null) null else (x_0 : T1,x_1 : T2,x_2 : T3,x_3 : T4,x_4 : T5,x_5 : T6) => ! this.scalaFunction(x_0,x_1,x_2,x_3,x_4,x_5), this.types, this.converter)
  
    def minimizing(minFunc : Term6[T1,T2,T3,T4,T5,T6,Int])(implicit asConstraint : t2c) : MinConstraint6[T1,T2,T3,T4,T5,T6] = {
      MinConstraint6[T1,T2,T3,T4,T5,T6](asConstraint(this), minFunc)
    }
  
    def lazySolve(implicit asConstraint: (Term6[T1,T2,T3,T4,T5,T6,R]) => Constraint6[T1,T2,T3,T4,T5,T6]): (L[T1],L[T2],L[T3],L[T4],L[T5],L[T6]) = {
      val constraint = asConstraint(this)
      val (constants, guards) = constantsAndGuards(constraint)
      (createL[T1](constraint, constants(0), guards(0)),createL[T2](constraint, constants(1), guards(1)),createL[T3](constraint, constants(2), guards(2)),createL[T4](constraint, constants(3), guards(3)),createL[T5](constraint, constants(4), guards(4)),createL[T6](constraint, constants(5), guards(5)))
    }
  
    def compose0[A1](other : Term1[A1, T1]) : Term6[A1, T2, T3, T4, T5, T6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 1, 6)
      Term6(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : T6) => this.scalaFunction(other.scalaFunction(x_0), x_1, x_2, x_3, x_4, x_5), newTypes, this.converter)
    }
    
    def compose1[A1](other : Term1[A1, T2]) : Term6[T1, A1, T3, T4, T5, T6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 1, 6)
      Term6(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : T6) => this.scalaFunction(x_0, other.scalaFunction(x_1), x_2, x_3, x_4, x_5), newTypes, this.converter)
    }
    
    def compose2[A1](other : Term1[A1, T3]) : Term6[T1, T2, A1, T4, T5, T6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 1, 6)
      Term6(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : T4, x_4 : T5, x_5 : T6) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2), x_3, x_4, x_5), newTypes, this.converter)
    }
    
    def compose3[A1](other : Term1[A1, T4]) : Term6[T1, T2, T3, A1, T5, T6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 3, 1, 6)
      Term6(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : A1, x_4 : T5, x_5 : T6) => this.scalaFunction(x_0, x_1, x_2, other.scalaFunction(x_3), x_4, x_5), newTypes, this.converter)
    }
    
    def compose4[A1](other : Term1[A1, T5]) : Term6[T1, T2, T3, T4, A1, T6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 4, 1, 6)
      Term6(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : A1, x_5 : T6) => this.scalaFunction(x_0, x_1, x_2, x_3, other.scalaFunction(x_4), x_5), newTypes, this.converter)
    }
    
    def compose5[A1](other : Term1[A1, T6]) : Term6[T1, T2, T3, T4, T5, A1, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 5, 1, 6)
      Term6(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : A1) => this.scalaFunction(x_0, x_1, x_2, x_3, x_4, other.scalaFunction(x_5)), newTypes, this.converter)
    }
    
    def compose0[A1, A2](other : Term2[A1, A2, T1]) : Term7[A1, A2, T2, T3, T4, T5, T6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 2, 6)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : T2, x_3 : T3, x_4 : T4, x_5 : T5, x_6 : T6) => this.scalaFunction(other.scalaFunction(x_0, x_1), x_2, x_3, x_4, x_5, x_6), newTypes, this.converter)
    }
    
    def compose1[A1, A2](other : Term2[A1, A2, T2]) : Term7[T1, A1, A2, T3, T4, T5, T6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 2, 6)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : T3, x_4 : T4, x_5 : T5, x_6 : T6) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2), x_3, x_4, x_5, x_6), newTypes, this.converter)
    }
    
    def compose2[A1, A2](other : Term2[A1, A2, T3]) : Term7[T1, T2, A1, A2, T4, T5, T6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 2, 6)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : A2, x_4 : T4, x_5 : T5, x_6 : T6) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2, x_3), x_4, x_5, x_6), newTypes, this.converter)
    }
    
    def compose3[A1, A2](other : Term2[A1, A2, T4]) : Term7[T1, T2, T3, A1, A2, T5, T6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 3, 2, 6)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : A1, x_4 : A2, x_5 : T5, x_6 : T6) => this.scalaFunction(x_0, x_1, x_2, other.scalaFunction(x_3, x_4), x_5, x_6), newTypes, this.converter)
    }
    
    def compose4[A1, A2](other : Term2[A1, A2, T5]) : Term7[T1, T2, T3, T4, A1, A2, T6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 4, 2, 6)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : A1, x_5 : A2, x_6 : T6) => this.scalaFunction(x_0, x_1, x_2, x_3, other.scalaFunction(x_4, x_5), x_6), newTypes, this.converter)
    }
    
    def compose5[A1, A2](other : Term2[A1, A2, T6]) : Term7[T1, T2, T3, T4, T5, A1, A2, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 5, 2, 6)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : A1, x_6 : A2) => this.scalaFunction(x_0, x_1, x_2, x_3, x_4, other.scalaFunction(x_5, x_6)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3](other : Term3[A1, A2, A3, T1]) : Term8[A1, A2, A3, T2, T3, T4, T5, T6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 3, 6)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : T2, x_4 : T3, x_5 : T4, x_6 : T5, x_7 : T6) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2), x_3, x_4, x_5, x_6, x_7), newTypes, this.converter)
    }
    
    def compose1[A1, A2, A3](other : Term3[A1, A2, A3, T2]) : Term8[T1, A1, A2, A3, T3, T4, T5, T6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 3, 6)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : A3, x_4 : T3, x_5 : T4, x_6 : T5, x_7 : T6) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2, x_3), x_4, x_5, x_6, x_7), newTypes, this.converter)
    }
    
    def compose2[A1, A2, A3](other : Term3[A1, A2, A3, T3]) : Term8[T1, T2, A1, A2, A3, T4, T5, T6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 3, 6)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : A2, x_4 : A3, x_5 : T4, x_6 : T5, x_7 : T6) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2, x_3, x_4), x_5, x_6, x_7), newTypes, this.converter)
    }
    
    def compose3[A1, A2, A3](other : Term3[A1, A2, A3, T4]) : Term8[T1, T2, T3, A1, A2, A3, T5, T6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 3, 3, 6)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : A1, x_4 : A2, x_5 : A3, x_6 : T5, x_7 : T6) => this.scalaFunction(x_0, x_1, x_2, other.scalaFunction(x_3, x_4, x_5), x_6, x_7), newTypes, this.converter)
    }
    
    def compose4[A1, A2, A3](other : Term3[A1, A2, A3, T5]) : Term8[T1, T2, T3, T4, A1, A2, A3, T6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 4, 3, 6)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : A1, x_5 : A2, x_6 : A3, x_7 : T6) => this.scalaFunction(x_0, x_1, x_2, x_3, other.scalaFunction(x_4, x_5, x_6), x_7), newTypes, this.converter)
    }
    
    def compose5[A1, A2, A3](other : Term3[A1, A2, A3, T6]) : Term8[T1, T2, T3, T4, T5, A1, A2, A3, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 5, 3, 6)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : A1, x_6 : A2, x_7 : A3) => this.scalaFunction(x_0, x_1, x_2, x_3, x_4, other.scalaFunction(x_5, x_6, x_7)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3, A4](other : Term4[A1, A2, A3, A4, T1]) : Term9[A1, A2, A3, A4, T2, T3, T4, T5, T6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 4, 6)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : A4, x_4 : T2, x_5 : T3, x_6 : T4, x_7 : T5, x_8 : T6) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2, x_3), x_4, x_5, x_6, x_7, x_8), newTypes, this.converter)
    }
    
    def compose1[A1, A2, A3, A4](other : Term4[A1, A2, A3, A4, T2]) : Term9[T1, A1, A2, A3, A4, T3, T4, T5, T6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 4, 6)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : A3, x_4 : A4, x_5 : T3, x_6 : T4, x_7 : T5, x_8 : T6) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2, x_3, x_4), x_5, x_6, x_7, x_8), newTypes, this.converter)
    }
    
    def compose2[A1, A2, A3, A4](other : Term4[A1, A2, A3, A4, T3]) : Term9[T1, T2, A1, A2, A3, A4, T4, T5, T6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 4, 6)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : A2, x_4 : A3, x_5 : A4, x_6 : T4, x_7 : T5, x_8 : T6) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2, x_3, x_4, x_5), x_6, x_7, x_8), newTypes, this.converter)
    }
    
    def compose3[A1, A2, A3, A4](other : Term4[A1, A2, A3, A4, T4]) : Term9[T1, T2, T3, A1, A2, A3, A4, T5, T6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 3, 4, 6)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : A1, x_4 : A2, x_5 : A3, x_6 : A4, x_7 : T5, x_8 : T6) => this.scalaFunction(x_0, x_1, x_2, other.scalaFunction(x_3, x_4, x_5, x_6), x_7, x_8), newTypes, this.converter)
    }
    
    def compose4[A1, A2, A3, A4](other : Term4[A1, A2, A3, A4, T5]) : Term9[T1, T2, T3, T4, A1, A2, A3, A4, T6, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 4, 4, 6)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : A1, x_5 : A2, x_6 : A3, x_7 : A4, x_8 : T6) => this.scalaFunction(x_0, x_1, x_2, x_3, other.scalaFunction(x_4, x_5, x_6, x_7), x_8), newTypes, this.converter)
    }
    
    def compose5[A1, A2, A3, A4](other : Term4[A1, A2, A3, A4, T6]) : Term9[T1, T2, T3, T4, T5, A1, A2, A3, A4, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 5, 4, 6)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : A1, x_6 : A2, x_7 : A3, x_8 : A4) => this.scalaFunction(x_0, x_1, x_2, x_3, x_4, other.scalaFunction(x_5, x_6, x_7, x_8)), newTypes, this.converter)
    }
  }
  
  trait Term7[T1,T2,T3,T4,T5,T6,T7,R] extends Term[(T1,T2,T3,T4,T5,T6,T7),R] with Function7[T1,T2,T3,T4,T5,T6,T7,R] {
    val convertingFunction = converterOf(this).exprSeq2scala7[T1,T2,T3,T4,T5,T6,T7] _
    type t2c = (Term7[T1,T2,T3,T4,T5,T6,T7,R]) => Term7[T1,T2,T3,T4,T5,T6,T7,Boolean]
    val scalaFunction : (T1,T2,T3,T4,T5,T6,T7) => R
    lazy val evaluator : (Seq[Expr]) => R = (s : Seq[Expr]) => scalaFunction(converter.expr2scala(s(0)).asInstanceOf[T1],converter.expr2scala(s(1)).asInstanceOf[T2],converter.expr2scala(s(2)).asInstanceOf[T3],converter.expr2scala(s(3)).asInstanceOf[T4],converter.expr2scala(s(4)).asInstanceOf[T5],converter.expr2scala(s(5)).asInstanceOf[T6],converter.expr2scala(s(6)).asInstanceOf[T7])
  
    override def apply(x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : T6, x_6 : T7) : R = scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5, x_6)
  
    def ||(other : Term7[T1,T2,T3,T4,T5,T6,T7,Boolean])(implicit asBoolean : (R) => Boolean) : Term7[T1,T2,T3,T4,T5,T6,T7,Boolean] = 
      Term7(this.program, Or(this.expr, other.expr), if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1,x_1 : T2,x_2 : T3,x_3 : T4,x_4 : T5,x_5 : T6,x_6 : T7) => this.scalaFunction(x_0,x_1,x_2,x_3,x_4,x_5,x_6) || other.scalaFunction(x_0,x_1,x_2,x_3,x_4,x_5,x_6), this.types, this.converter)
  
    def &&(other : Term7[T1,T2,T3,T4,T5,T6,T7,Boolean])(implicit asBoolean : (R) => Boolean) : Term7[T1,T2,T3,T4,T5,T6,T7,Boolean] = 
      Term7(this.program, And(this.expr, other.expr), if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1,x_1 : T2,x_2 : T3,x_3 : T4,x_4 : T5,x_5 : T6,x_6 : T7) => this.scalaFunction(x_0,x_1,x_2,x_3,x_4,x_5,x_6) && other.scalaFunction(x_0,x_1,x_2,x_3,x_4,x_5,x_6), this.types, this.converter)
  
    def unary_!(implicit asBoolean : (R) => Boolean) : Term7[T1,T2,T3,T4,T5,T6,T7,Boolean] = 
      Term7(this.program, Not(this.expr), if (this.scalaFunction == null) null else (x_0 : T1,x_1 : T2,x_2 : T3,x_3 : T4,x_4 : T5,x_5 : T6,x_6 : T7) => ! this.scalaFunction(x_0,x_1,x_2,x_3,x_4,x_5,x_6), this.types, this.converter)
  
    def minimizing(minFunc : Term7[T1,T2,T3,T4,T5,T6,T7,Int])(implicit asConstraint : t2c) : MinConstraint7[T1,T2,T3,T4,T5,T6,T7] = {
      MinConstraint7[T1,T2,T3,T4,T5,T6,T7](asConstraint(this), minFunc)
    }
  
    def lazySolve(implicit asConstraint: (Term7[T1,T2,T3,T4,T5,T6,T7,R]) => Constraint7[T1,T2,T3,T4,T5,T6,T7]): (L[T1],L[T2],L[T3],L[T4],L[T5],L[T6],L[T7]) = {
      val constraint = asConstraint(this)
      val (constants, guards) = constantsAndGuards(constraint)
      (createL[T1](constraint, constants(0), guards(0)),createL[T2](constraint, constants(1), guards(1)),createL[T3](constraint, constants(2), guards(2)),createL[T4](constraint, constants(3), guards(3)),createL[T5](constraint, constants(4), guards(4)),createL[T6](constraint, constants(5), guards(5)),createL[T7](constraint, constants(6), guards(6)))
    }
  
    def compose0[A1](other : Term1[A1, T1]) : Term7[A1, T2, T3, T4, T5, T6, T7, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 1, 7)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : T6, x_6 : T7) => this.scalaFunction(other.scalaFunction(x_0), x_1, x_2, x_3, x_4, x_5, x_6), newTypes, this.converter)
    }
    
    def compose1[A1](other : Term1[A1, T2]) : Term7[T1, A1, T3, T4, T5, T6, T7, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 1, 7)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : T6, x_6 : T7) => this.scalaFunction(x_0, other.scalaFunction(x_1), x_2, x_3, x_4, x_5, x_6), newTypes, this.converter)
    }
    
    def compose2[A1](other : Term1[A1, T3]) : Term7[T1, T2, A1, T4, T5, T6, T7, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 1, 7)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : T4, x_4 : T5, x_5 : T6, x_6 : T7) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2), x_3, x_4, x_5, x_6), newTypes, this.converter)
    }
    
    def compose3[A1](other : Term1[A1, T4]) : Term7[T1, T2, T3, A1, T5, T6, T7, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 3, 1, 7)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : A1, x_4 : T5, x_5 : T6, x_6 : T7) => this.scalaFunction(x_0, x_1, x_2, other.scalaFunction(x_3), x_4, x_5, x_6), newTypes, this.converter)
    }
    
    def compose4[A1](other : Term1[A1, T5]) : Term7[T1, T2, T3, T4, A1, T6, T7, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 4, 1, 7)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : A1, x_5 : T6, x_6 : T7) => this.scalaFunction(x_0, x_1, x_2, x_3, other.scalaFunction(x_4), x_5, x_6), newTypes, this.converter)
    }
    
    def compose5[A1](other : Term1[A1, T6]) : Term7[T1, T2, T3, T4, T5, A1, T7, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 5, 1, 7)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : A1, x_6 : T7) => this.scalaFunction(x_0, x_1, x_2, x_3, x_4, other.scalaFunction(x_5), x_6), newTypes, this.converter)
    }
    
    def compose6[A1](other : Term1[A1, T7]) : Term7[T1, T2, T3, T4, T5, T6, A1, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 6, 1, 7)
      Term7(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : T6, x_6 : A1) => this.scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5, other.scalaFunction(x_6)), newTypes, this.converter)
    }
    
    def compose0[A1, A2](other : Term2[A1, A2, T1]) : Term8[A1, A2, T2, T3, T4, T5, T6, T7, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 2, 7)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : T2, x_3 : T3, x_4 : T4, x_5 : T5, x_6 : T6, x_7 : T7) => this.scalaFunction(other.scalaFunction(x_0, x_1), x_2, x_3, x_4, x_5, x_6, x_7), newTypes, this.converter)
    }
    
    def compose1[A1, A2](other : Term2[A1, A2, T2]) : Term8[T1, A1, A2, T3, T4, T5, T6, T7, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 2, 7)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : T3, x_4 : T4, x_5 : T5, x_6 : T6, x_7 : T7) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2), x_3, x_4, x_5, x_6, x_7), newTypes, this.converter)
    }
    
    def compose2[A1, A2](other : Term2[A1, A2, T3]) : Term8[T1, T2, A1, A2, T4, T5, T6, T7, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 2, 7)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : A2, x_4 : T4, x_5 : T5, x_6 : T6, x_7 : T7) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2, x_3), x_4, x_5, x_6, x_7), newTypes, this.converter)
    }
    
    def compose3[A1, A2](other : Term2[A1, A2, T4]) : Term8[T1, T2, T3, A1, A2, T5, T6, T7, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 3, 2, 7)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : A1, x_4 : A2, x_5 : T5, x_6 : T6, x_7 : T7) => this.scalaFunction(x_0, x_1, x_2, other.scalaFunction(x_3, x_4), x_5, x_6, x_7), newTypes, this.converter)
    }
    
    def compose4[A1, A2](other : Term2[A1, A2, T5]) : Term8[T1, T2, T3, T4, A1, A2, T6, T7, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 4, 2, 7)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : A1, x_5 : A2, x_6 : T6, x_7 : T7) => this.scalaFunction(x_0, x_1, x_2, x_3, other.scalaFunction(x_4, x_5), x_6, x_7), newTypes, this.converter)
    }
    
    def compose5[A1, A2](other : Term2[A1, A2, T6]) : Term8[T1, T2, T3, T4, T5, A1, A2, T7, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 5, 2, 7)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : A1, x_6 : A2, x_7 : T7) => this.scalaFunction(x_0, x_1, x_2, x_3, x_4, other.scalaFunction(x_5, x_6), x_7), newTypes, this.converter)
    }
    
    def compose6[A1, A2](other : Term2[A1, A2, T7]) : Term8[T1, T2, T3, T4, T5, T6, A1, A2, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 6, 2, 7)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : T6, x_6 : A1, x_7 : A2) => this.scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5, other.scalaFunction(x_6, x_7)), newTypes, this.converter)
    }
    
    def compose0[A1, A2, A3](other : Term3[A1, A2, A3, T1]) : Term9[A1, A2, A3, T2, T3, T4, T5, T6, T7, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 3, 7)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : A3, x_3 : T2, x_4 : T3, x_5 : T4, x_6 : T5, x_7 : T6, x_8 : T7) => this.scalaFunction(other.scalaFunction(x_0, x_1, x_2), x_3, x_4, x_5, x_6, x_7, x_8), newTypes, this.converter)
    }
    
    def compose1[A1, A2, A3](other : Term3[A1, A2, A3, T2]) : Term9[T1, A1, A2, A3, T3, T4, T5, T6, T7, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 3, 7)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : A3, x_4 : T3, x_5 : T4, x_6 : T5, x_7 : T6, x_8 : T7) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2, x_3), x_4, x_5, x_6, x_7, x_8), newTypes, this.converter)
    }
    
    def compose2[A1, A2, A3](other : Term3[A1, A2, A3, T3]) : Term9[T1, T2, A1, A2, A3, T4, T5, T6, T7, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 3, 7)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : A2, x_4 : A3, x_5 : T4, x_6 : T5, x_7 : T6, x_8 : T7) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2, x_3, x_4), x_5, x_6, x_7, x_8), newTypes, this.converter)
    }
    
    def compose3[A1, A2, A3](other : Term3[A1, A2, A3, T4]) : Term9[T1, T2, T3, A1, A2, A3, T5, T6, T7, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 3, 3, 7)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : A1, x_4 : A2, x_5 : A3, x_6 : T5, x_7 : T6, x_8 : T7) => this.scalaFunction(x_0, x_1, x_2, other.scalaFunction(x_3, x_4, x_5), x_6, x_7, x_8), newTypes, this.converter)
    }
    
    def compose4[A1, A2, A3](other : Term3[A1, A2, A3, T5]) : Term9[T1, T2, T3, T4, A1, A2, A3, T6, T7, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 4, 3, 7)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : A1, x_5 : A2, x_6 : A3, x_7 : T6, x_8 : T7) => this.scalaFunction(x_0, x_1, x_2, x_3, other.scalaFunction(x_4, x_5, x_6), x_7, x_8), newTypes, this.converter)
    }
    
    def compose5[A1, A2, A3](other : Term3[A1, A2, A3, T6]) : Term9[T1, T2, T3, T4, T5, A1, A2, A3, T7, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 5, 3, 7)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : A1, x_6 : A2, x_7 : A3, x_8 : T7) => this.scalaFunction(x_0, x_1, x_2, x_3, x_4, other.scalaFunction(x_5, x_6, x_7), x_8), newTypes, this.converter)
    }
    
    def compose6[A1, A2, A3](other : Term3[A1, A2, A3, T7]) : Term9[T1, T2, T3, T4, T5, T6, A1, A2, A3, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 6, 3, 7)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : T6, x_6 : A1, x_7 : A2, x_8 : A3) => this.scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5, other.scalaFunction(x_6, x_7, x_8)), newTypes, this.converter)
    }
  }
  
  trait Term8[T1,T2,T3,T4,T5,T6,T7,T8,R] extends Term[(T1,T2,T3,T4,T5,T6,T7,T8),R] with Function8[T1,T2,T3,T4,T5,T6,T7,T8,R] {
    val convertingFunction = converterOf(this).exprSeq2scala8[T1,T2,T3,T4,T5,T6,T7,T8] _
    type t2c = (Term8[T1,T2,T3,T4,T5,T6,T7,T8,R]) => Term8[T1,T2,T3,T4,T5,T6,T7,T8,Boolean]
    val scalaFunction : (T1,T2,T3,T4,T5,T6,T7,T8) => R
    lazy val evaluator : (Seq[Expr]) => R = (s : Seq[Expr]) => scalaFunction(converter.expr2scala(s(0)).asInstanceOf[T1],converter.expr2scala(s(1)).asInstanceOf[T2],converter.expr2scala(s(2)).asInstanceOf[T3],converter.expr2scala(s(3)).asInstanceOf[T4],converter.expr2scala(s(4)).asInstanceOf[T5],converter.expr2scala(s(5)).asInstanceOf[T6],converter.expr2scala(s(6)).asInstanceOf[T7],converter.expr2scala(s(7)).asInstanceOf[T8])
  
    override def apply(x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : T6, x_6 : T7, x_7 : T8) : R = scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7)
  
    def ||(other : Term8[T1,T2,T3,T4,T5,T6,T7,T8,Boolean])(implicit asBoolean : (R) => Boolean) : Term8[T1,T2,T3,T4,T5,T6,T7,T8,Boolean] = 
      Term8(this.program, Or(this.expr, other.expr), if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1,x_1 : T2,x_2 : T3,x_3 : T4,x_4 : T5,x_5 : T6,x_6 : T7,x_7 : T8) => this.scalaFunction(x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7) || other.scalaFunction(x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7), this.types, this.converter)
  
    def &&(other : Term8[T1,T2,T3,T4,T5,T6,T7,T8,Boolean])(implicit asBoolean : (R) => Boolean) : Term8[T1,T2,T3,T4,T5,T6,T7,T8,Boolean] = 
      Term8(this.program, And(this.expr, other.expr), if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1,x_1 : T2,x_2 : T3,x_3 : T4,x_4 : T5,x_5 : T6,x_6 : T7,x_7 : T8) => this.scalaFunction(x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7) && other.scalaFunction(x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7), this.types, this.converter)
  
    def unary_!(implicit asBoolean : (R) => Boolean) : Term8[T1,T2,T3,T4,T5,T6,T7,T8,Boolean] = 
      Term8(this.program, Not(this.expr), if (this.scalaFunction == null) null else (x_0 : T1,x_1 : T2,x_2 : T3,x_3 : T4,x_4 : T5,x_5 : T6,x_6 : T7,x_7 : T8) => ! this.scalaFunction(x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7), this.types, this.converter)
  
    def minimizing(minFunc : Term8[T1,T2,T3,T4,T5,T6,T7,T8,Int])(implicit asConstraint : t2c) : MinConstraint8[T1,T2,T3,T4,T5,T6,T7,T8] = {
      MinConstraint8[T1,T2,T3,T4,T5,T6,T7,T8](asConstraint(this), minFunc)
    }
  
    def lazySolve(implicit asConstraint: (Term8[T1,T2,T3,T4,T5,T6,T7,T8,R]) => Constraint8[T1,T2,T3,T4,T5,T6,T7,T8]): (L[T1],L[T2],L[T3],L[T4],L[T5],L[T6],L[T7],L[T8]) = {
      val constraint = asConstraint(this)
      val (constants, guards) = constantsAndGuards(constraint)
      (createL[T1](constraint, constants(0), guards(0)),createL[T2](constraint, constants(1), guards(1)),createL[T3](constraint, constants(2), guards(2)),createL[T4](constraint, constants(3), guards(3)),createL[T5](constraint, constants(4), guards(4)),createL[T6](constraint, constants(5), guards(5)),createL[T7](constraint, constants(6), guards(6)),createL[T8](constraint, constants(7), guards(7)))
    }
  
    def compose0[A1](other : Term1[A1, T1]) : Term8[A1, T2, T3, T4, T5, T6, T7, T8, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 1, 8)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : T6, x_6 : T7, x_7 : T8) => this.scalaFunction(other.scalaFunction(x_0), x_1, x_2, x_3, x_4, x_5, x_6, x_7), newTypes, this.converter)
    }
    
    def compose1[A1](other : Term1[A1, T2]) : Term8[T1, A1, T3, T4, T5, T6, T7, T8, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 1, 8)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : T6, x_6 : T7, x_7 : T8) => this.scalaFunction(x_0, other.scalaFunction(x_1), x_2, x_3, x_4, x_5, x_6, x_7), newTypes, this.converter)
    }
    
    def compose2[A1](other : Term1[A1, T3]) : Term8[T1, T2, A1, T4, T5, T6, T7, T8, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 1, 8)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : T4, x_4 : T5, x_5 : T6, x_6 : T7, x_7 : T8) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2), x_3, x_4, x_5, x_6, x_7), newTypes, this.converter)
    }
    
    def compose3[A1](other : Term1[A1, T4]) : Term8[T1, T2, T3, A1, T5, T6, T7, T8, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 3, 1, 8)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : A1, x_4 : T5, x_5 : T6, x_6 : T7, x_7 : T8) => this.scalaFunction(x_0, x_1, x_2, other.scalaFunction(x_3), x_4, x_5, x_6, x_7), newTypes, this.converter)
    }
    
    def compose4[A1](other : Term1[A1, T5]) : Term8[T1, T2, T3, T4, A1, T6, T7, T8, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 4, 1, 8)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : A1, x_5 : T6, x_6 : T7, x_7 : T8) => this.scalaFunction(x_0, x_1, x_2, x_3, other.scalaFunction(x_4), x_5, x_6, x_7), newTypes, this.converter)
    }
    
    def compose5[A1](other : Term1[A1, T6]) : Term8[T1, T2, T3, T4, T5, A1, T7, T8, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 5, 1, 8)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : A1, x_6 : T7, x_7 : T8) => this.scalaFunction(x_0, x_1, x_2, x_3, x_4, other.scalaFunction(x_5), x_6, x_7), newTypes, this.converter)
    }
    
    def compose6[A1](other : Term1[A1, T7]) : Term8[T1, T2, T3, T4, T5, T6, A1, T8, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 6, 1, 8)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : T6, x_6 : A1, x_7 : T8) => this.scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5, other.scalaFunction(x_6), x_7), newTypes, this.converter)
    }
    
    def compose7[A1](other : Term1[A1, T8]) : Term8[T1, T2, T3, T4, T5, T6, T7, A1, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 7, 1, 8)
      Term8(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : T6, x_6 : T7, x_7 : A1) => this.scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5, x_6, other.scalaFunction(x_7)), newTypes, this.converter)
    }
    
    def compose0[A1, A2](other : Term2[A1, A2, T1]) : Term9[A1, A2, T2, T3, T4, T5, T6, T7, T8, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 2, 8)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : A2, x_2 : T2, x_3 : T3, x_4 : T4, x_5 : T5, x_6 : T6, x_7 : T7, x_8 : T8) => this.scalaFunction(other.scalaFunction(x_0, x_1), x_2, x_3, x_4, x_5, x_6, x_7, x_8), newTypes, this.converter)
    }
    
    def compose1[A1, A2](other : Term2[A1, A2, T2]) : Term9[T1, A1, A2, T3, T4, T5, T6, T7, T8, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 2, 8)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : A2, x_3 : T3, x_4 : T4, x_5 : T5, x_6 : T6, x_7 : T7, x_8 : T8) => this.scalaFunction(x_0, other.scalaFunction(x_1, x_2), x_3, x_4, x_5, x_6, x_7, x_8), newTypes, this.converter)
    }
    
    def compose2[A1, A2](other : Term2[A1, A2, T3]) : Term9[T1, T2, A1, A2, T4, T5, T6, T7, T8, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 2, 8)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : A2, x_4 : T4, x_5 : T5, x_6 : T6, x_7 : T7, x_8 : T8) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2, x_3), x_4, x_5, x_6, x_7, x_8), newTypes, this.converter)
    }
    
    def compose3[A1, A2](other : Term2[A1, A2, T4]) : Term9[T1, T2, T3, A1, A2, T5, T6, T7, T8, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 3, 2, 8)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : A1, x_4 : A2, x_5 : T5, x_6 : T6, x_7 : T7, x_8 : T8) => this.scalaFunction(x_0, x_1, x_2, other.scalaFunction(x_3, x_4), x_5, x_6, x_7, x_8), newTypes, this.converter)
    }
    
    def compose4[A1, A2](other : Term2[A1, A2, T5]) : Term9[T1, T2, T3, T4, A1, A2, T6, T7, T8, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 4, 2, 8)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : A1, x_5 : A2, x_6 : T6, x_7 : T7, x_8 : T8) => this.scalaFunction(x_0, x_1, x_2, x_3, other.scalaFunction(x_4, x_5), x_6, x_7, x_8), newTypes, this.converter)
    }
    
    def compose5[A1, A2](other : Term2[A1, A2, T6]) : Term9[T1, T2, T3, T4, T5, A1, A2, T7, T8, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 5, 2, 8)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : A1, x_6 : A2, x_7 : T7, x_8 : T8) => this.scalaFunction(x_0, x_1, x_2, x_3, x_4, other.scalaFunction(x_5, x_6), x_7, x_8), newTypes, this.converter)
    }
    
    def compose6[A1, A2](other : Term2[A1, A2, T7]) : Term9[T1, T2, T3, T4, T5, T6, A1, A2, T8, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 6, 2, 8)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : T6, x_6 : A1, x_7 : A2, x_8 : T8) => this.scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5, other.scalaFunction(x_6, x_7), x_8), newTypes, this.converter)
    }
    
    def compose7[A1, A2](other : Term2[A1, A2, T8]) : Term9[T1, T2, T3, T4, T5, T6, T7, A1, A2, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 7, 2, 8)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : T6, x_6 : T7, x_7 : A1, x_8 : A2) => this.scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5, x_6, other.scalaFunction(x_7, x_8)), newTypes, this.converter)
    }
  }
  
  trait Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,R] extends Term[(T1,T2,T3,T4,T5,T6,T7,T8,T9),R] with Function9[T1,T2,T3,T4,T5,T6,T7,T8,T9,R] {
    val convertingFunction = converterOf(this).exprSeq2scala9[T1,T2,T3,T4,T5,T6,T7,T8,T9] _
    type t2c = (Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,R]) => Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,Boolean]
    val scalaFunction : (T1,T2,T3,T4,T5,T6,T7,T8,T9) => R
    lazy val evaluator : (Seq[Expr]) => R = (s : Seq[Expr]) => scalaFunction(converter.expr2scala(s(0)).asInstanceOf[T1],converter.expr2scala(s(1)).asInstanceOf[T2],converter.expr2scala(s(2)).asInstanceOf[T3],converter.expr2scala(s(3)).asInstanceOf[T4],converter.expr2scala(s(4)).asInstanceOf[T5],converter.expr2scala(s(5)).asInstanceOf[T6],converter.expr2scala(s(6)).asInstanceOf[T7],converter.expr2scala(s(7)).asInstanceOf[T8],converter.expr2scala(s(8)).asInstanceOf[T9])
  
    override def apply(x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : T6, x_6 : T7, x_7 : T8, x_8 : T9) : R = scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8)
  
    def ||(other : Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,Boolean])(implicit asBoolean : (R) => Boolean) : Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,Boolean] = 
      Term9(this.program, Or(this.expr, other.expr), if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1,x_1 : T2,x_2 : T3,x_3 : T4,x_4 : T5,x_5 : T6,x_6 : T7,x_7 : T8,x_8 : T9) => this.scalaFunction(x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7,x_8) || other.scalaFunction(x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7,x_8), this.types, this.converter)
  
    def &&(other : Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,Boolean])(implicit asBoolean : (R) => Boolean) : Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,Boolean] = 
      Term9(this.program, And(this.expr, other.expr), if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1,x_1 : T2,x_2 : T3,x_3 : T4,x_4 : T5,x_5 : T6,x_6 : T7,x_7 : T8,x_8 : T9) => this.scalaFunction(x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7,x_8) && other.scalaFunction(x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7,x_8), this.types, this.converter)
  
    def unary_!(implicit asBoolean : (R) => Boolean) : Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,Boolean] = 
      Term9(this.program, Not(this.expr), if (this.scalaFunction == null) null else (x_0 : T1,x_1 : T2,x_2 : T3,x_3 : T4,x_4 : T5,x_5 : T6,x_6 : T7,x_7 : T8,x_8 : T9) => ! this.scalaFunction(x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7,x_8), this.types, this.converter)
  
    def minimizing(minFunc : Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,Int])(implicit asConstraint : t2c) : MinConstraint9[T1,T2,T3,T4,T5,T6,T7,T8,T9] = {
      MinConstraint9[T1,T2,T3,T4,T5,T6,T7,T8,T9](asConstraint(this), minFunc)
    }
  
    def lazySolve(implicit asConstraint: (Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,R]) => Constraint9[T1,T2,T3,T4,T5,T6,T7,T8,T9]): (L[T1],L[T2],L[T3],L[T4],L[T5],L[T6],L[T7],L[T8],L[T9]) = {
      val constraint = asConstraint(this)
      val (constants, guards) = constantsAndGuards(constraint)
      (createL[T1](constraint, constants(0), guards(0)),createL[T2](constraint, constants(1), guards(1)),createL[T3](constraint, constants(2), guards(2)),createL[T4](constraint, constants(3), guards(3)),createL[T5](constraint, constants(4), guards(4)),createL[T6](constraint, constants(5), guards(5)),createL[T7](constraint, constants(6), guards(6)),createL[T8](constraint, constants(7), guards(7)),createL[T9](constraint, constants(8), guards(8)))
    }
  
    def compose0[A1](other : Term1[A1, T1]) : Term9[A1, T2, T3, T4, T5, T6, T7, T8, T9, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 0, 1, 9)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : A1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : T6, x_6 : T7, x_7 : T8, x_8 : T9) => this.scalaFunction(other.scalaFunction(x_0), x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8), newTypes, this.converter)
    }
    
    def compose1[A1](other : Term1[A1, T2]) : Term9[T1, A1, T3, T4, T5, T6, T7, T8, T9, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 1, 1, 9)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : A1, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : T6, x_6 : T7, x_7 : T8, x_8 : T9) => this.scalaFunction(x_0, other.scalaFunction(x_1), x_2, x_3, x_4, x_5, x_6, x_7, x_8), newTypes, this.converter)
    }
    
    def compose2[A1](other : Term1[A1, T3]) : Term9[T1, T2, A1, T4, T5, T6, T7, T8, T9, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 2, 1, 9)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : A1, x_3 : T4, x_4 : T5, x_5 : T6, x_6 : T7, x_7 : T8, x_8 : T9) => this.scalaFunction(x_0, x_1, other.scalaFunction(x_2), x_3, x_4, x_5, x_6, x_7, x_8), newTypes, this.converter)
    }
    
    def compose3[A1](other : Term1[A1, T4]) : Term9[T1, T2, T3, A1, T5, T6, T7, T8, T9, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 3, 1, 9)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : A1, x_4 : T5, x_5 : T6, x_6 : T7, x_7 : T8, x_8 : T9) => this.scalaFunction(x_0, x_1, x_2, other.scalaFunction(x_3), x_4, x_5, x_6, x_7, x_8), newTypes, this.converter)
    }
    
    def compose4[A1](other : Term1[A1, T5]) : Term9[T1, T2, T3, T4, A1, T6, T7, T8, T9, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 4, 1, 9)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : A1, x_5 : T6, x_6 : T7, x_7 : T8, x_8 : T9) => this.scalaFunction(x_0, x_1, x_2, x_3, other.scalaFunction(x_4), x_5, x_6, x_7, x_8), newTypes, this.converter)
    }
    
    def compose5[A1](other : Term1[A1, T6]) : Term9[T1, T2, T3, T4, T5, A1, T7, T8, T9, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 5, 1, 9)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : A1, x_6 : T7, x_7 : T8, x_8 : T9) => this.scalaFunction(x_0, x_1, x_2, x_3, x_4, other.scalaFunction(x_5), x_6, x_7, x_8), newTypes, this.converter)
    }
    
    def compose6[A1](other : Term1[A1, T7]) : Term9[T1, T2, T3, T4, T5, T6, A1, T8, T9, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 6, 1, 9)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : T6, x_6 : A1, x_7 : T8, x_8 : T9) => this.scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5, other.scalaFunction(x_6), x_7, x_8), newTypes, this.converter)
    }
    
    def compose7[A1](other : Term1[A1, T8]) : Term9[T1, T2, T3, T4, T5, T6, T7, A1, T9, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 7, 1, 9)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : T6, x_6 : T7, x_7 : A1, x_8 : T9) => this.scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5, x_6, other.scalaFunction(x_7), x_8), newTypes, this.converter)
    }
    
    def compose8[A1](other : Term1[A1, T9]) : Term9[T1, T2, T3, T4, T5, T6, T7, T8, A1, R] = {
      val (newExpr, newTypes) = Terms.compose(other, this, 8, 1, 9)
      Term9(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (x_0 : T1, x_1 : T2, x_2 : T3, x_3 : T4, x_4 : T5, x_5 : T6, x_6 : T7, x_7 : T8, x_8 : A1) => this.scalaFunction(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, other.scalaFunction(x_8)), newTypes, this.converter)
    }
  }
  
  object Term1 {
    def apply[T1,R](conv : Converter, serializedProg : Serialized, serializedInputVars: Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr], scalaExpr : (T1) => R) = {
      val (converter, program, expr, types) = Term.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new Term[(T1),R](program, expr, types, converter) with Term1[T1,R] {
        val scalaFunction = scalaExpr
      }
    }
    
    def apply[T1,R](program : Program, expr : Expr, scalaExpr : (T1) => R, types : Seq[TypeTree], converter : Converter) =
      new Term[(T1),R](program, expr, types, converter) with Term1[T1,R] {
        val scalaFunction = scalaExpr
      }
  }
  
  object Term2 {
    def apply[T1,T2,R](conv : Converter, serializedProg : Serialized, serializedInputVars: Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr], scalaExpr : (T1,T2) => R) = {
      val (converter, program, expr, types) = Term.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new Term[(T1,T2),R](program, expr, types, converter) with Term2[T1,T2,R] {
        val scalaFunction = scalaExpr
      }
    }
    
    def apply[T1,T2,R](program : Program, expr : Expr, scalaExpr : (T1,T2) => R, types : Seq[TypeTree], converter : Converter) =
      new Term[(T1,T2),R](program, expr, types, converter) with Term2[T1,T2,R] {
        val scalaFunction = scalaExpr
      }
  }
  
  object Term3 {
    def apply[T1,T2,T3,R](conv : Converter, serializedProg : Serialized, serializedInputVars: Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr], scalaExpr : (T1,T2,T3) => R) = {
      val (converter, program, expr, types) = Term.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new Term[(T1,T2,T3),R](program, expr, types, converter) with Term3[T1,T2,T3,R] {
        val scalaFunction = scalaExpr
      }
    }
    
    def apply[T1,T2,T3,R](program : Program, expr : Expr, scalaExpr : (T1,T2,T3) => R, types : Seq[TypeTree], converter : Converter) =
      new Term[(T1,T2,T3),R](program, expr, types, converter) with Term3[T1,T2,T3,R] {
        val scalaFunction = scalaExpr
      }
  }
  
  object Term4 {
    def apply[T1,T2,T3,T4,R](conv : Converter, serializedProg : Serialized, serializedInputVars: Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr], scalaExpr : (T1,T2,T3,T4) => R) = {
      val (converter, program, expr, types) = Term.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new Term[(T1,T2,T3,T4),R](program, expr, types, converter) with Term4[T1,T2,T3,T4,R] {
        val scalaFunction = scalaExpr
      }
    }
    
    def apply[T1,T2,T3,T4,R](program : Program, expr : Expr, scalaExpr : (T1,T2,T3,T4) => R, types : Seq[TypeTree], converter : Converter) =
      new Term[(T1,T2,T3,T4),R](program, expr, types, converter) with Term4[T1,T2,T3,T4,R] {
        val scalaFunction = scalaExpr
      }
  }
  
  object Term5 {
    def apply[T1,T2,T3,T4,T5,R](conv : Converter, serializedProg : Serialized, serializedInputVars: Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr], scalaExpr : (T1,T2,T3,T4,T5) => R) = {
      val (converter, program, expr, types) = Term.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new Term[(T1,T2,T3,T4,T5),R](program, expr, types, converter) with Term5[T1,T2,T3,T4,T5,R] {
        val scalaFunction = scalaExpr
      }
    }
    
    def apply[T1,T2,T3,T4,T5,R](program : Program, expr : Expr, scalaExpr : (T1,T2,T3,T4,T5) => R, types : Seq[TypeTree], converter : Converter) =
      new Term[(T1,T2,T3,T4,T5),R](program, expr, types, converter) with Term5[T1,T2,T3,T4,T5,R] {
        val scalaFunction = scalaExpr
      }
  }
  
  object Term6 {
    def apply[T1,T2,T3,T4,T5,T6,R](conv : Converter, serializedProg : Serialized, serializedInputVars: Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr], scalaExpr : (T1,T2,T3,T4,T5,T6) => R) = {
      val (converter, program, expr, types) = Term.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new Term[(T1,T2,T3,T4,T5,T6),R](program, expr, types, converter) with Term6[T1,T2,T3,T4,T5,T6,R] {
        val scalaFunction = scalaExpr
      }
    }
    
    def apply[T1,T2,T3,T4,T5,T6,R](program : Program, expr : Expr, scalaExpr : (T1,T2,T3,T4,T5,T6) => R, types : Seq[TypeTree], converter : Converter) =
      new Term[(T1,T2,T3,T4,T5,T6),R](program, expr, types, converter) with Term6[T1,T2,T3,T4,T5,T6,R] {
        val scalaFunction = scalaExpr
      }
  }
  
  object Term7 {
    def apply[T1,T2,T3,T4,T5,T6,T7,R](conv : Converter, serializedProg : Serialized, serializedInputVars: Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr], scalaExpr : (T1,T2,T3,T4,T5,T6,T7) => R) = {
      val (converter, program, expr, types) = Term.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new Term[(T1,T2,T3,T4,T5,T6,T7),R](program, expr, types, converter) with Term7[T1,T2,T3,T4,T5,T6,T7,R] {
        val scalaFunction = scalaExpr
      }
    }
    
    def apply[T1,T2,T3,T4,T5,T6,T7,R](program : Program, expr : Expr, scalaExpr : (T1,T2,T3,T4,T5,T6,T7) => R, types : Seq[TypeTree], converter : Converter) =
      new Term[(T1,T2,T3,T4,T5,T6,T7),R](program, expr, types, converter) with Term7[T1,T2,T3,T4,T5,T6,T7,R] {
        val scalaFunction = scalaExpr
      }
  }
  
  object Term8 {
    def apply[T1,T2,T3,T4,T5,T6,T7,T8,R](conv : Converter, serializedProg : Serialized, serializedInputVars: Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr], scalaExpr : (T1,T2,T3,T4,T5,T6,T7,T8) => R) = {
      val (converter, program, expr, types) = Term.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new Term[(T1,T2,T3,T4,T5,T6,T7,T8),R](program, expr, types, converter) with Term8[T1,T2,T3,T4,T5,T6,T7,T8,R] {
        val scalaFunction = scalaExpr
      }
    }
    
    def apply[T1,T2,T3,T4,T5,T6,T7,T8,R](program : Program, expr : Expr, scalaExpr : (T1,T2,T3,T4,T5,T6,T7,T8) => R, types : Seq[TypeTree], converter : Converter) =
      new Term[(T1,T2,T3,T4,T5,T6,T7,T8),R](program, expr, types, converter) with Term8[T1,T2,T3,T4,T5,T6,T7,T8,R] {
        val scalaFunction = scalaExpr
      }
  }
  
  object Term9 {
    def apply[T1,T2,T3,T4,T5,T6,T7,T8,T9,R](conv : Converter, serializedProg : Serialized, serializedInputVars: Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr], scalaExpr : (T1,T2,T3,T4,T5,T6,T7,T8,T9) => R) = {
      val (converter, program, expr, types) = Term.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new Term[(T1,T2,T3,T4,T5,T6,T7,T8,T9),R](program, expr, types, converter) with Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,R] {
        val scalaFunction = scalaExpr
      }
    }
    
    def apply[T1,T2,T3,T4,T5,T6,T7,T8,T9,R](program : Program, expr : Expr, scalaExpr : (T1,T2,T3,T4,T5,T6,T7,T8,T9) => R, types : Seq[TypeTree], converter : Converter) =
      new Term[(T1,T2,T3,T4,T5,T6,T7,T8,T9),R](program, expr, types, converter) with Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,R] {
        val scalaFunction = scalaExpr
      }
  }
  
  case class MinConstraint1[T1](cons : Term1[T1,Boolean], minFunc : Term1[T1,Int]) extends MinConstraint[(T1)](cons, minFunc) {
    val convertingFunction = converterOf(cons).exprSeq2scala1[T1] _
  }
  
  case class MinConstraint2[T1,T2](cons : Term2[T1,T2,Boolean], minFunc : Term2[T1,T2,Int]) extends MinConstraint[(T1,T2)](cons, minFunc) {
    val convertingFunction = converterOf(cons).exprSeq2scala2[T1,T2] _
  }
  
  case class MinConstraint3[T1,T2,T3](cons : Term3[T1,T2,T3,Boolean], minFunc : Term3[T1,T2,T3,Int]) extends MinConstraint[(T1,T2,T3)](cons, minFunc) {
    val convertingFunction = converterOf(cons).exprSeq2scala3[T1,T2,T3] _
  }
  
  case class MinConstraint4[T1,T2,T3,T4](cons : Term4[T1,T2,T3,T4,Boolean], minFunc : Term4[T1,T2,T3,T4,Int]) extends MinConstraint[(T1,T2,T3,T4)](cons, minFunc) {
    val convertingFunction = converterOf(cons).exprSeq2scala4[T1,T2,T3,T4] _
  }
  
  case class MinConstraint5[T1,T2,T3,T4,T5](cons : Term5[T1,T2,T3,T4,T5,Boolean], minFunc : Term5[T1,T2,T3,T4,T5,Int]) extends MinConstraint[(T1,T2,T3,T4,T5)](cons, minFunc) {
    val convertingFunction = converterOf(cons).exprSeq2scala5[T1,T2,T3,T4,T5] _
  }
  
  case class MinConstraint6[T1,T2,T3,T4,T5,T6](cons : Term6[T1,T2,T3,T4,T5,T6,Boolean], minFunc : Term6[T1,T2,T3,T4,T5,T6,Int]) extends MinConstraint[(T1,T2,T3,T4,T5,T6)](cons, minFunc) {
    val convertingFunction = converterOf(cons).exprSeq2scala6[T1,T2,T3,T4,T5,T6] _
  }
  
  case class MinConstraint7[T1,T2,T3,T4,T5,T6,T7](cons : Term7[T1,T2,T3,T4,T5,T6,T7,Boolean], minFunc : Term7[T1,T2,T3,T4,T5,T6,T7,Int]) extends MinConstraint[(T1,T2,T3,T4,T5,T6,T7)](cons, minFunc) {
    val convertingFunction = converterOf(cons).exprSeq2scala7[T1,T2,T3,T4,T5,T6,T7] _
  }
  
  case class MinConstraint8[T1,T2,T3,T4,T5,T6,T7,T8](cons : Term8[T1,T2,T3,T4,T5,T6,T7,T8,Boolean], minFunc : Term8[T1,T2,T3,T4,T5,T6,T7,T8,Int]) extends MinConstraint[(T1,T2,T3,T4,T5,T6,T7,T8)](cons, minFunc) {
    val convertingFunction = converterOf(cons).exprSeq2scala8[T1,T2,T3,T4,T5,T6,T7,T8] _
  }
  
  case class MinConstraint9[T1,T2,T3,T4,T5,T6,T7,T8,T9](cons : Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,Boolean], minFunc : Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,Int]) extends MinConstraint[(T1,T2,T3,T4,T5,T6,T7,T8,T9)](cons, minFunc) {
    val convertingFunction = converterOf(cons).exprSeq2scala9[T1,T2,T3,T4,T5,T6,T7,T8,T9] _
  }
  /** END OF GENERATED CODE. */

  /** Compute composed expression for g∘f */
  private def compose(f : Term[_,_], g : Term[_,_], index : Int, nf : Int, ng : Int) : (Expr, Seq[TypeTree]) = {
    val deBruijnF = f.types.zipWithIndex.map{ case (t,i) => DeBruijnIndex(i).setType(t) }
    val deBruijnG = g.types.zipWithIndex.map{ case (t,i) => DeBruijnIndex(i).setType(t) }
    assert(deBruijnF.size == nf && deBruijnG.size == ng)

    val substG : Map[Expr,Expr] = deBruijnG.drop(index + 1).map{ case d @ DeBruijnIndex(i) => (d, DeBruijnIndex(i + nf - 1).setType(d.getType)) }.toMap
    val substF : Map[Expr,Expr] = deBruijnF.map{ case d @ DeBruijnIndex(i) => (d, DeBruijnIndex(i + index).setType(d.getType)) }.toMap

    val renamedExprF = replace(substF, f.expr)
    val renamedExprG = replace(substG, g.expr)

    val indexToReplace = deBruijnG(index)
    val newExpr   = replace(Map(indexToReplace -> renamedExprF), renamedExprG)
    val newTypes  = g.types.take(index) ++ f.types ++ g.types.drop(index + 1)
    assert(newTypes.size == nf + ng - 1)
    (newExpr, newTypes)
  }

  def converterOf(term : Term[_,_]) : Converter = term.converter

  def typesOf(term : Term[_,_]) : Seq[TypeTree] = term.types

  def exprOf(term : Term[_,_]) : Expr = term.expr

  def programOf(term : Term[_,_]) : Program = term.program

  /** Compute a fresh sequence of output variables and the combined expression
   * containing those */
  def combineConstraint(constraint : Constraint[_]) : (Seq[Identifier], Expr) = {
    val expr = exprOf(constraint)

    val outputVarTypes = typesOf(constraint)

    val freshOutputIDs = outputVarTypes.zipWithIndex.map{ case (t, idx) => FreshIdentifier("x" + idx, true).setType(t) }
    val deBruijnIndices = outputVarTypes.zipWithIndex.map{ case (t, idx) => DeBruijnIndex(idx).setType(t) }
    val exprWithFreshIDs = replace((deBruijnIndices zip (freshOutputIDs map (Variable(_)))).toMap, expr)

    (freshOutputIDs, exprWithFreshIDs)
  }

}
