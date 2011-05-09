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

  /** A constraint is just a term with Boolean range */
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

  sealed trait Term1[T1,R] extends Term[(T1),R] {
    val convertingFunction = converterOf(this).exprSeq2scala1[T1] _
    type t2c = (Term1[T1,R]) => Term1[T1,Boolean]
    
    def ||(other : Term1[T1,Boolean])(implicit asConstraint : t2c) : Term1[T1,Boolean] = OrConstraint1[T1](this, other)

    def &&(other : Term1[T1,Boolean])(implicit asConstraint : t2c) : Term1[T1,Boolean] = AndConstraint1[T1](this, other)

    def unary_!(implicit asConstraint : t2c) : Term1[T1,Boolean] = NotConstraint1[T1](this)

    def minimizing(minFunc : Term1[T1,Int])(implicit asConstraint : t2c) : MinConstraint1[T1] = {
      MinConstraint1[T1](asConstraint(this), minFunc)
    }

    def compose0[A1](other : Term1[A1,T1]) : Term1[A1,R] = compose_0_1_1(other, this)
    def compose0[A1,A2](other : Term2[A1,A2,T1]) : Term2[A1,A2,R] = compose_0_2_1(other, this)
    def compose0[A1,A2,A3](other : Term3[A1,A2,A3,T1]) : Term3[A1,A2,A3,R] = compose_0_3_1(other, this)
    def compose0[A1,A2,A3,A4](other : Term4[A1,A2,A3,A4,T1]) : Term4[A1,A2,A3,A4,R] = compose_0_4_1(other, this)
    def compose0[A1,A2,A3,A4,A5](other : Term5[A1,A2,A3,A4,A5,T1]) : Term5[A1,A2,A3,A4,A5,R] = compose_0_5_1(other, this)
    def compose0[A1,A2,A3,A4,A5,A6](other : Term6[A1,A2,A3,A4,A5,A6,T1]) : Term6[A1,A2,A3,A4,A5,A6,R] = compose_0_6_1(other, this)
    def compose0[A1,A2,A3,A4,A5,A6,A7](other : Term7[A1,A2,A3,A4,A5,A6,A7,T1]) : Term7[A1,A2,A3,A4,A5,A6,A7,R] = compose_0_7_1(other, this)
    def compose0[A1,A2,A3,A4,A5,A6,A7,A8](other : Term8[A1,A2,A3,A4,A5,A6,A7,A8,T1]) : Term8[A1,A2,A3,A4,A5,A6,A7,A8,R] = compose_0_8_1(other, this)
    def compose0[A1,A2,A3,A4,A5,A6,A7,A8,A9](other : Term9[A1,A2,A3,A4,A5,A6,A7,A8,A9,T1]) : Term9[A1,A2,A3,A4,A5,A6,A7,A8,A9,R] = compose_0_9_1(other, this)
  }

  sealed trait Term2[T1,T2,R] extends Term[(T1,T2),R] {
    val convertingFunction = converterOf(this).exprSeq2scala2[T1,T2] _
    type t2c = (Term2[T1,T2,R]) => Term2[T1,T2,Boolean]
    
    def ||(other : Term2[T1,T2,Boolean])(implicit asConstraint : t2c) : Term2[T1,T2,Boolean] = OrConstraint2[T1,T2](this, other)

    def &&(other : Term2[T1,T2,Boolean])(implicit asConstraint : t2c) : Term2[T1,T2,Boolean] = AndConstraint2[T1,T2](this, other)

    def unary_!(implicit asConstraint : t2c) : Term2[T1,T2,Boolean] = NotConstraint2[T1,T2](this)

    def minimizing(minFunc : Term2[T1,T2,Int])(implicit asConstraint : t2c) : MinConstraint2[T1,T2] = {
      MinConstraint2[T1,T2](asConstraint(this), minFunc)
    }

    def compose0[A1](other : Term1[A1,T1]) : Term2[A1,T2,R] = compose_0_1_2(other, this)
    def compose1[A1](other : Term1[A1,T2]) : Term2[T1,A1,R] = compose_1_1_2(other, this)
    def compose0[A1,A2](other : Term2[A1,A2,T1]) : Term3[A1,A2,T2,R] = compose_0_2_2(other, this)
    def compose1[A1,A2](other : Term2[A1,A2,T2]) : Term3[T1,A1,A2,R] = compose_1_2_2(other, this)
    def compose0[A1,A2,A3](other : Term3[A1,A2,A3,T1]) : Term4[A1,A2,A3,T2,R] = compose_0_3_2(other, this)
    def compose1[A1,A2,A3](other : Term3[A1,A2,A3,T2]) : Term4[T1,A1,A2,A3,R] = compose_1_3_2(other, this)
    def compose0[A1,A2,A3,A4](other : Term4[A1,A2,A3,A4,T1]) : Term5[A1,A2,A3,A4,T2,R] = compose_0_4_2(other, this)
    def compose1[A1,A2,A3,A4](other : Term4[A1,A2,A3,A4,T2]) : Term5[T1,A1,A2,A3,A4,R] = compose_1_4_2(other, this)
    def compose0[A1,A2,A3,A4,A5](other : Term5[A1,A2,A3,A4,A5,T1]) : Term6[A1,A2,A3,A4,A5,T2,R] = compose_0_5_2(other, this)
    def compose1[A1,A2,A3,A4,A5](other : Term5[A1,A2,A3,A4,A5,T2]) : Term6[T1,A1,A2,A3,A4,A5,R] = compose_1_5_2(other, this)
    def compose0[A1,A2,A3,A4,A5,A6](other : Term6[A1,A2,A3,A4,A5,A6,T1]) : Term7[A1,A2,A3,A4,A5,A6,T2,R] = compose_0_6_2(other, this)
    def compose1[A1,A2,A3,A4,A5,A6](other : Term6[A1,A2,A3,A4,A5,A6,T2]) : Term7[T1,A1,A2,A3,A4,A5,A6,R] = compose_1_6_2(other, this)
    def compose0[A1,A2,A3,A4,A5,A6,A7](other : Term7[A1,A2,A3,A4,A5,A6,A7,T1]) : Term8[A1,A2,A3,A4,A5,A6,A7,T2,R] = compose_0_7_2(other, this)
    def compose1[A1,A2,A3,A4,A5,A6,A7](other : Term7[A1,A2,A3,A4,A5,A6,A7,T2]) : Term8[T1,A1,A2,A3,A4,A5,A6,A7,R] = compose_1_7_2(other, this)
    def compose0[A1,A2,A3,A4,A5,A6,A7,A8](other : Term8[A1,A2,A3,A4,A5,A6,A7,A8,T1]) : Term9[A1,A2,A3,A4,A5,A6,A7,A8,T2,R] = compose_0_8_2(other, this)
    def compose1[A1,A2,A3,A4,A5,A6,A7,A8](other : Term8[A1,A2,A3,A4,A5,A6,A7,A8,T2]) : Term9[T1,A1,A2,A3,A4,A5,A6,A7,A8,R] = compose_1_8_2(other, this)
  }

  sealed trait Term3[T1,T2,T3,R] extends Term[(T1,T2,T3),R] {
    val convertingFunction = converterOf(this).exprSeq2scala3[T1,T2,T3] _
    type t2c = (Term3[T1,T2,T3,R]) => Term3[T1,T2,T3,Boolean]
    
    def ||(other : Term3[T1,T2,T3,Boolean])(implicit asConstraint : t2c) : Term3[T1,T2,T3,Boolean] = OrConstraint3[T1,T2,T3](this, other)

    def &&(other : Term3[T1,T2,T3,Boolean])(implicit asConstraint : t2c) : Term3[T1,T2,T3,Boolean] = AndConstraint3[T1,T2,T3](this, other)

    def unary_!(implicit asConstraint : t2c) : Term3[T1,T2,T3,Boolean] = NotConstraint3[T1,T2,T3](this)

    def minimizing(minFunc : Term3[T1,T2,T3,Int])(implicit asConstraint : t2c) : MinConstraint3[T1,T2,T3] = {
      MinConstraint3[T1,T2,T3](asConstraint(this), minFunc)
    }

    def compose0[A1](other : Term1[A1,T1]) : Term3[A1,T2,T3,R] = compose_0_1_3(other, this)
    def compose1[A1](other : Term1[A1,T2]) : Term3[T1,A1,T3,R] = compose_1_1_3(other, this)
    def compose2[A1](other : Term1[A1,T3]) : Term3[T1,T2,A1,R] = compose_2_1_3(other, this)
    def compose0[A1,A2](other : Term2[A1,A2,T1]) : Term4[A1,A2,T2,T3,R] = compose_0_2_3(other, this)
    def compose1[A1,A2](other : Term2[A1,A2,T2]) : Term4[T1,A1,A2,T3,R] = compose_1_2_3(other, this)
    def compose2[A1,A2](other : Term2[A1,A2,T3]) : Term4[T1,T2,A1,A2,R] = compose_2_2_3(other, this)
    def compose0[A1,A2,A3](other : Term3[A1,A2,A3,T1]) : Term5[A1,A2,A3,T2,T3,R] = compose_0_3_3(other, this)
    def compose1[A1,A2,A3](other : Term3[A1,A2,A3,T2]) : Term5[T1,A1,A2,A3,T3,R] = compose_1_3_3(other, this)
    def compose2[A1,A2,A3](other : Term3[A1,A2,A3,T3]) : Term5[T1,T2,A1,A2,A3,R] = compose_2_3_3(other, this)
    def compose0[A1,A2,A3,A4](other : Term4[A1,A2,A3,A4,T1]) : Term6[A1,A2,A3,A4,T2,T3,R] = compose_0_4_3(other, this)
    def compose1[A1,A2,A3,A4](other : Term4[A1,A2,A3,A4,T2]) : Term6[T1,A1,A2,A3,A4,T3,R] = compose_1_4_3(other, this)
    def compose2[A1,A2,A3,A4](other : Term4[A1,A2,A3,A4,T3]) : Term6[T1,T2,A1,A2,A3,A4,R] = compose_2_4_3(other, this)
    def compose0[A1,A2,A3,A4,A5](other : Term5[A1,A2,A3,A4,A5,T1]) : Term7[A1,A2,A3,A4,A5,T2,T3,R] = compose_0_5_3(other, this)
    def compose1[A1,A2,A3,A4,A5](other : Term5[A1,A2,A3,A4,A5,T2]) : Term7[T1,A1,A2,A3,A4,A5,T3,R] = compose_1_5_3(other, this)
    def compose2[A1,A2,A3,A4,A5](other : Term5[A1,A2,A3,A4,A5,T3]) : Term7[T1,T2,A1,A2,A3,A4,A5,R] = compose_2_5_3(other, this)
    def compose0[A1,A2,A3,A4,A5,A6](other : Term6[A1,A2,A3,A4,A5,A6,T1]) : Term8[A1,A2,A3,A4,A5,A6,T2,T3,R] = compose_0_6_3(other, this)
    def compose1[A1,A2,A3,A4,A5,A6](other : Term6[A1,A2,A3,A4,A5,A6,T2]) : Term8[T1,A1,A2,A3,A4,A5,A6,T3,R] = compose_1_6_3(other, this)
    def compose2[A1,A2,A3,A4,A5,A6](other : Term6[A1,A2,A3,A4,A5,A6,T3]) : Term8[T1,T2,A1,A2,A3,A4,A5,A6,R] = compose_2_6_3(other, this)
    def compose0[A1,A2,A3,A4,A5,A6,A7](other : Term7[A1,A2,A3,A4,A5,A6,A7,T1]) : Term9[A1,A2,A3,A4,A5,A6,A7,T2,T3,R] = compose_0_7_3(other, this)
    def compose1[A1,A2,A3,A4,A5,A6,A7](other : Term7[A1,A2,A3,A4,A5,A6,A7,T2]) : Term9[T1,A1,A2,A3,A4,A5,A6,A7,T3,R] = compose_1_7_3(other, this)
    def compose2[A1,A2,A3,A4,A5,A6,A7](other : Term7[A1,A2,A3,A4,A5,A6,A7,T3]) : Term9[T1,T2,A1,A2,A3,A4,A5,A6,A7,R] = compose_2_7_3(other, this)
  }

  sealed trait Term4[T1,T2,T3,T4,R] extends Term[(T1,T2,T3,T4),R] {
    val convertingFunction = converterOf(this).exprSeq2scala4[T1,T2,T3,T4] _
    type t2c = (Term4[T1,T2,T3,T4,R]) => Term4[T1,T2,T3,T4,Boolean]
    
    def ||(other : Term4[T1,T2,T3,T4,Boolean])(implicit asConstraint : t2c) : Term4[T1,T2,T3,T4,Boolean] = OrConstraint4[T1,T2,T3,T4](this, other)

    def &&(other : Term4[T1,T2,T3,T4,Boolean])(implicit asConstraint : t2c) : Term4[T1,T2,T3,T4,Boolean] = AndConstraint4[T1,T2,T3,T4](this, other)

    def unary_!(implicit asConstraint : t2c) : Term4[T1,T2,T3,T4,Boolean] = NotConstraint4[T1,T2,T3,T4](this)

    def minimizing(minFunc : Term4[T1,T2,T3,T4,Int])(implicit asConstraint : t2c) : MinConstraint4[T1,T2,T3,T4] = {
      MinConstraint4[T1,T2,T3,T4](asConstraint(this), minFunc)
    }

    def compose0[A1](other : Term1[A1,T1]) : Term4[A1,T2,T3,T4,R] = compose_0_1_4(other, this)
    def compose1[A1](other : Term1[A1,T2]) : Term4[T1,A1,T3,T4,R] = compose_1_1_4(other, this)
    def compose2[A1](other : Term1[A1,T3]) : Term4[T1,T2,A1,T4,R] = compose_2_1_4(other, this)
    def compose3[A1](other : Term1[A1,T4]) : Term4[T1,T2,T3,A1,R] = compose_3_1_4(other, this)
    def compose0[A1,A2](other : Term2[A1,A2,T1]) : Term5[A1,A2,T2,T3,T4,R] = compose_0_2_4(other, this)
    def compose1[A1,A2](other : Term2[A1,A2,T2]) : Term5[T1,A1,A2,T3,T4,R] = compose_1_2_4(other, this)
    def compose2[A1,A2](other : Term2[A1,A2,T3]) : Term5[T1,T2,A1,A2,T4,R] = compose_2_2_4(other, this)
    def compose3[A1,A2](other : Term2[A1,A2,T4]) : Term5[T1,T2,T3,A1,A2,R] = compose_3_2_4(other, this)
    def compose0[A1,A2,A3](other : Term3[A1,A2,A3,T1]) : Term6[A1,A2,A3,T2,T3,T4,R] = compose_0_3_4(other, this)
    def compose1[A1,A2,A3](other : Term3[A1,A2,A3,T2]) : Term6[T1,A1,A2,A3,T3,T4,R] = compose_1_3_4(other, this)
    def compose2[A1,A2,A3](other : Term3[A1,A2,A3,T3]) : Term6[T1,T2,A1,A2,A3,T4,R] = compose_2_3_4(other, this)
    def compose3[A1,A2,A3](other : Term3[A1,A2,A3,T4]) : Term6[T1,T2,T3,A1,A2,A3,R] = compose_3_3_4(other, this)
    def compose0[A1,A2,A3,A4](other : Term4[A1,A2,A3,A4,T1]) : Term7[A1,A2,A3,A4,T2,T3,T4,R] = compose_0_4_4(other, this)
    def compose1[A1,A2,A3,A4](other : Term4[A1,A2,A3,A4,T2]) : Term7[T1,A1,A2,A3,A4,T3,T4,R] = compose_1_4_4(other, this)
    def compose2[A1,A2,A3,A4](other : Term4[A1,A2,A3,A4,T3]) : Term7[T1,T2,A1,A2,A3,A4,T4,R] = compose_2_4_4(other, this)
    def compose3[A1,A2,A3,A4](other : Term4[A1,A2,A3,A4,T4]) : Term7[T1,T2,T3,A1,A2,A3,A4,R] = compose_3_4_4(other, this)
    def compose0[A1,A2,A3,A4,A5](other : Term5[A1,A2,A3,A4,A5,T1]) : Term8[A1,A2,A3,A4,A5,T2,T3,T4,R] = compose_0_5_4(other, this)
    def compose1[A1,A2,A3,A4,A5](other : Term5[A1,A2,A3,A4,A5,T2]) : Term8[T1,A1,A2,A3,A4,A5,T3,T4,R] = compose_1_5_4(other, this)
    def compose2[A1,A2,A3,A4,A5](other : Term5[A1,A2,A3,A4,A5,T3]) : Term8[T1,T2,A1,A2,A3,A4,A5,T4,R] = compose_2_5_4(other, this)
    def compose3[A1,A2,A3,A4,A5](other : Term5[A1,A2,A3,A4,A5,T4]) : Term8[T1,T2,T3,A1,A2,A3,A4,A5,R] = compose_3_5_4(other, this)
    def compose0[A1,A2,A3,A4,A5,A6](other : Term6[A1,A2,A3,A4,A5,A6,T1]) : Term9[A1,A2,A3,A4,A5,A6,T2,T3,T4,R] = compose_0_6_4(other, this)
    def compose1[A1,A2,A3,A4,A5,A6](other : Term6[A1,A2,A3,A4,A5,A6,T2]) : Term9[T1,A1,A2,A3,A4,A5,A6,T3,T4,R] = compose_1_6_4(other, this)
    def compose2[A1,A2,A3,A4,A5,A6](other : Term6[A1,A2,A3,A4,A5,A6,T3]) : Term9[T1,T2,A1,A2,A3,A4,A5,A6,T4,R] = compose_2_6_4(other, this)
    def compose3[A1,A2,A3,A4,A5,A6](other : Term6[A1,A2,A3,A4,A5,A6,T4]) : Term9[T1,T2,T3,A1,A2,A3,A4,A5,A6,R] = compose_3_6_4(other, this)
  }

  sealed trait Term5[T1,T2,T3,T4,T5,R] extends Term[(T1,T2,T3,T4,T5),R] {
    val convertingFunction = converterOf(this).exprSeq2scala5[T1,T2,T3,T4,T5] _
    type t2c = (Term5[T1,T2,T3,T4,T5,R]) => Term5[T1,T2,T3,T4,T5,Boolean]
    
    def ||(other : Term5[T1,T2,T3,T4,T5,Boolean])(implicit asConstraint : t2c) : Term5[T1,T2,T3,T4,T5,Boolean] = OrConstraint5[T1,T2,T3,T4,T5](this, other)

    def &&(other : Term5[T1,T2,T3,T4,T5,Boolean])(implicit asConstraint : t2c) : Term5[T1,T2,T3,T4,T5,Boolean] = AndConstraint5[T1,T2,T3,T4,T5](this, other)

    def unary_!(implicit asConstraint : t2c) : Term5[T1,T2,T3,T4,T5,Boolean] = NotConstraint5[T1,T2,T3,T4,T5](this)

    def minimizing(minFunc : Term5[T1,T2,T3,T4,T5,Int])(implicit asConstraint : t2c) : MinConstraint5[T1,T2,T3,T4,T5] = {
      MinConstraint5[T1,T2,T3,T4,T5](asConstraint(this), minFunc)
    }

    def compose0[A1](other : Term1[A1,T1]) : Term5[A1,T2,T3,T4,T5,R] = compose_0_1_5(other, this)
    def compose1[A1](other : Term1[A1,T2]) : Term5[T1,A1,T3,T4,T5,R] = compose_1_1_5(other, this)
    def compose2[A1](other : Term1[A1,T3]) : Term5[T1,T2,A1,T4,T5,R] = compose_2_1_5(other, this)
    def compose3[A1](other : Term1[A1,T4]) : Term5[T1,T2,T3,A1,T5,R] = compose_3_1_5(other, this)
    def compose4[A1](other : Term1[A1,T5]) : Term5[T1,T2,T3,T4,A1,R] = compose_4_1_5(other, this)
    def compose0[A1,A2](other : Term2[A1,A2,T1]) : Term6[A1,A2,T2,T3,T4,T5,R] = compose_0_2_5(other, this)
    def compose1[A1,A2](other : Term2[A1,A2,T2]) : Term6[T1,A1,A2,T3,T4,T5,R] = compose_1_2_5(other, this)
    def compose2[A1,A2](other : Term2[A1,A2,T3]) : Term6[T1,T2,A1,A2,T4,T5,R] = compose_2_2_5(other, this)
    def compose3[A1,A2](other : Term2[A1,A2,T4]) : Term6[T1,T2,T3,A1,A2,T5,R] = compose_3_2_5(other, this)
    def compose4[A1,A2](other : Term2[A1,A2,T5]) : Term6[T1,T2,T3,T4,A1,A2,R] = compose_4_2_5(other, this)
    def compose0[A1,A2,A3](other : Term3[A1,A2,A3,T1]) : Term7[A1,A2,A3,T2,T3,T4,T5,R] = compose_0_3_5(other, this)
    def compose1[A1,A2,A3](other : Term3[A1,A2,A3,T2]) : Term7[T1,A1,A2,A3,T3,T4,T5,R] = compose_1_3_5(other, this)
    def compose2[A1,A2,A3](other : Term3[A1,A2,A3,T3]) : Term7[T1,T2,A1,A2,A3,T4,T5,R] = compose_2_3_5(other, this)
    def compose3[A1,A2,A3](other : Term3[A1,A2,A3,T4]) : Term7[T1,T2,T3,A1,A2,A3,T5,R] = compose_3_3_5(other, this)
    def compose4[A1,A2,A3](other : Term3[A1,A2,A3,T5]) : Term7[T1,T2,T3,T4,A1,A2,A3,R] = compose_4_3_5(other, this)
    def compose0[A1,A2,A3,A4](other : Term4[A1,A2,A3,A4,T1]) : Term8[A1,A2,A3,A4,T2,T3,T4,T5,R] = compose_0_4_5(other, this)
    def compose1[A1,A2,A3,A4](other : Term4[A1,A2,A3,A4,T2]) : Term8[T1,A1,A2,A3,A4,T3,T4,T5,R] = compose_1_4_5(other, this)
    def compose2[A1,A2,A3,A4](other : Term4[A1,A2,A3,A4,T3]) : Term8[T1,T2,A1,A2,A3,A4,T4,T5,R] = compose_2_4_5(other, this)
    def compose3[A1,A2,A3,A4](other : Term4[A1,A2,A3,A4,T4]) : Term8[T1,T2,T3,A1,A2,A3,A4,T5,R] = compose_3_4_5(other, this)
    def compose4[A1,A2,A3,A4](other : Term4[A1,A2,A3,A4,T5]) : Term8[T1,T2,T3,T4,A1,A2,A3,A4,R] = compose_4_4_5(other, this)
    def compose0[A1,A2,A3,A4,A5](other : Term5[A1,A2,A3,A4,A5,T1]) : Term9[A1,A2,A3,A4,A5,T2,T3,T4,T5,R] = compose_0_5_5(other, this)
    def compose1[A1,A2,A3,A4,A5](other : Term5[A1,A2,A3,A4,A5,T2]) : Term9[T1,A1,A2,A3,A4,A5,T3,T4,T5,R] = compose_1_5_5(other, this)
    def compose2[A1,A2,A3,A4,A5](other : Term5[A1,A2,A3,A4,A5,T3]) : Term9[T1,T2,A1,A2,A3,A4,A5,T4,T5,R] = compose_2_5_5(other, this)
    def compose3[A1,A2,A3,A4,A5](other : Term5[A1,A2,A3,A4,A5,T4]) : Term9[T1,T2,T3,A1,A2,A3,A4,A5,T5,R] = compose_3_5_5(other, this)
    def compose4[A1,A2,A3,A4,A5](other : Term5[A1,A2,A3,A4,A5,T5]) : Term9[T1,T2,T3,T4,A1,A2,A3,A4,A5,R] = compose_4_5_5(other, this)
  }

  sealed trait Term6[T1,T2,T3,T4,T5,T6,R] extends Term[(T1,T2,T3,T4,T5,T6),R] {
    val convertingFunction = converterOf(this).exprSeq2scala6[T1,T2,T3,T4,T5,T6] _
    type t2c = (Term6[T1,T2,T3,T4,T5,T6,R]) => Term6[T1,T2,T3,T4,T5,T6,Boolean]
    
    def ||(other : Term6[T1,T2,T3,T4,T5,T6,Boolean])(implicit asConstraint : t2c) : Term6[T1,T2,T3,T4,T5,T6,Boolean] = OrConstraint6[T1,T2,T3,T4,T5,T6](this, other)

    def &&(other : Term6[T1,T2,T3,T4,T5,T6,Boolean])(implicit asConstraint : t2c) : Term6[T1,T2,T3,T4,T5,T6,Boolean] = AndConstraint6[T1,T2,T3,T4,T5,T6](this, other)

    def unary_!(implicit asConstraint : t2c) : Term6[T1,T2,T3,T4,T5,T6,Boolean] = NotConstraint6[T1,T2,T3,T4,T5,T6](this)

    def minimizing(minFunc : Term6[T1,T2,T3,T4,T5,T6,Int])(implicit asConstraint : t2c) : MinConstraint6[T1,T2,T3,T4,T5,T6] = {
      MinConstraint6[T1,T2,T3,T4,T5,T6](asConstraint(this), minFunc)
    }

    def compose0[A1](other : Term1[A1,T1]) : Term6[A1,T2,T3,T4,T5,T6,R] = compose_0_1_6(other, this)
    def compose1[A1](other : Term1[A1,T2]) : Term6[T1,A1,T3,T4,T5,T6,R] = compose_1_1_6(other, this)
    def compose2[A1](other : Term1[A1,T3]) : Term6[T1,T2,A1,T4,T5,T6,R] = compose_2_1_6(other, this)
    def compose3[A1](other : Term1[A1,T4]) : Term6[T1,T2,T3,A1,T5,T6,R] = compose_3_1_6(other, this)
    def compose4[A1](other : Term1[A1,T5]) : Term6[T1,T2,T3,T4,A1,T6,R] = compose_4_1_6(other, this)
    def compose5[A1](other : Term1[A1,T6]) : Term6[T1,T2,T3,T4,T5,A1,R] = compose_5_1_6(other, this)
    def compose0[A1,A2](other : Term2[A1,A2,T1]) : Term7[A1,A2,T2,T3,T4,T5,T6,R] = compose_0_2_6(other, this)
    def compose1[A1,A2](other : Term2[A1,A2,T2]) : Term7[T1,A1,A2,T3,T4,T5,T6,R] = compose_1_2_6(other, this)
    def compose2[A1,A2](other : Term2[A1,A2,T3]) : Term7[T1,T2,A1,A2,T4,T5,T6,R] = compose_2_2_6(other, this)
    def compose3[A1,A2](other : Term2[A1,A2,T4]) : Term7[T1,T2,T3,A1,A2,T5,T6,R] = compose_3_2_6(other, this)
    def compose4[A1,A2](other : Term2[A1,A2,T5]) : Term7[T1,T2,T3,T4,A1,A2,T6,R] = compose_4_2_6(other, this)
    def compose5[A1,A2](other : Term2[A1,A2,T6]) : Term7[T1,T2,T3,T4,T5,A1,A2,R] = compose_5_2_6(other, this)
    def compose0[A1,A2,A3](other : Term3[A1,A2,A3,T1]) : Term8[A1,A2,A3,T2,T3,T4,T5,T6,R] = compose_0_3_6(other, this)
    def compose1[A1,A2,A3](other : Term3[A1,A2,A3,T2]) : Term8[T1,A1,A2,A3,T3,T4,T5,T6,R] = compose_1_3_6(other, this)
    def compose2[A1,A2,A3](other : Term3[A1,A2,A3,T3]) : Term8[T1,T2,A1,A2,A3,T4,T5,T6,R] = compose_2_3_6(other, this)
    def compose3[A1,A2,A3](other : Term3[A1,A2,A3,T4]) : Term8[T1,T2,T3,A1,A2,A3,T5,T6,R] = compose_3_3_6(other, this)
    def compose4[A1,A2,A3](other : Term3[A1,A2,A3,T5]) : Term8[T1,T2,T3,T4,A1,A2,A3,T6,R] = compose_4_3_6(other, this)
    def compose5[A1,A2,A3](other : Term3[A1,A2,A3,T6]) : Term8[T1,T2,T3,T4,T5,A1,A2,A3,R] = compose_5_3_6(other, this)
    def compose0[A1,A2,A3,A4](other : Term4[A1,A2,A3,A4,T1]) : Term9[A1,A2,A3,A4,T2,T3,T4,T5,T6,R] = compose_0_4_6(other, this)
    def compose1[A1,A2,A3,A4](other : Term4[A1,A2,A3,A4,T2]) : Term9[T1,A1,A2,A3,A4,T3,T4,T5,T6,R] = compose_1_4_6(other, this)
    def compose2[A1,A2,A3,A4](other : Term4[A1,A2,A3,A4,T3]) : Term9[T1,T2,A1,A2,A3,A4,T4,T5,T6,R] = compose_2_4_6(other, this)
    def compose3[A1,A2,A3,A4](other : Term4[A1,A2,A3,A4,T4]) : Term9[T1,T2,T3,A1,A2,A3,A4,T5,T6,R] = compose_3_4_6(other, this)
    def compose4[A1,A2,A3,A4](other : Term4[A1,A2,A3,A4,T5]) : Term9[T1,T2,T3,T4,A1,A2,A3,A4,T6,R] = compose_4_4_6(other, this)
    def compose5[A1,A2,A3,A4](other : Term4[A1,A2,A3,A4,T6]) : Term9[T1,T2,T3,T4,T5,A1,A2,A3,A4,R] = compose_5_4_6(other, this)
  }

  sealed trait Term7[T1,T2,T3,T4,T5,T6,T7,R] extends Term[(T1,T2,T3,T4,T5,T6,T7),R] {
    val convertingFunction = converterOf(this).exprSeq2scala7[T1,T2,T3,T4,T5,T6,T7] _
    type t2c = (Term7[T1,T2,T3,T4,T5,T6,T7,R]) => Term7[T1,T2,T3,T4,T5,T6,T7,Boolean]
    
    def ||(other : Term7[T1,T2,T3,T4,T5,T6,T7,Boolean])(implicit asConstraint : t2c) : Term7[T1,T2,T3,T4,T5,T6,T7,Boolean] = OrConstraint7[T1,T2,T3,T4,T5,T6,T7](this, other)

    def &&(other : Term7[T1,T2,T3,T4,T5,T6,T7,Boolean])(implicit asConstraint : t2c) : Term7[T1,T2,T3,T4,T5,T6,T7,Boolean] = AndConstraint7[T1,T2,T3,T4,T5,T6,T7](this, other)

    def unary_!(implicit asConstraint : t2c) : Term7[T1,T2,T3,T4,T5,T6,T7,Boolean] = NotConstraint7[T1,T2,T3,T4,T5,T6,T7](this)

    def minimizing(minFunc : Term7[T1,T2,T3,T4,T5,T6,T7,Int])(implicit asConstraint : t2c) : MinConstraint7[T1,T2,T3,T4,T5,T6,T7] = {
      MinConstraint7[T1,T2,T3,T4,T5,T6,T7](asConstraint(this), minFunc)
    }

    def compose0[A1](other : Term1[A1,T1]) : Term7[A1,T2,T3,T4,T5,T6,T7,R] = compose_0_1_7(other, this)
    def compose1[A1](other : Term1[A1,T2]) : Term7[T1,A1,T3,T4,T5,T6,T7,R] = compose_1_1_7(other, this)
    def compose2[A1](other : Term1[A1,T3]) : Term7[T1,T2,A1,T4,T5,T6,T7,R] = compose_2_1_7(other, this)
    def compose3[A1](other : Term1[A1,T4]) : Term7[T1,T2,T3,A1,T5,T6,T7,R] = compose_3_1_7(other, this)
    def compose4[A1](other : Term1[A1,T5]) : Term7[T1,T2,T3,T4,A1,T6,T7,R] = compose_4_1_7(other, this)
    def compose5[A1](other : Term1[A1,T6]) : Term7[T1,T2,T3,T4,T5,A1,T7,R] = compose_5_1_7(other, this)
    def compose6[A1](other : Term1[A1,T7]) : Term7[T1,T2,T3,T4,T5,T6,A1,R] = compose_6_1_7(other, this)
    def compose0[A1,A2](other : Term2[A1,A2,T1]) : Term8[A1,A2,T2,T3,T4,T5,T6,T7,R] = compose_0_2_7(other, this)
    def compose1[A1,A2](other : Term2[A1,A2,T2]) : Term8[T1,A1,A2,T3,T4,T5,T6,T7,R] = compose_1_2_7(other, this)
    def compose2[A1,A2](other : Term2[A1,A2,T3]) : Term8[T1,T2,A1,A2,T4,T5,T6,T7,R] = compose_2_2_7(other, this)
    def compose3[A1,A2](other : Term2[A1,A2,T4]) : Term8[T1,T2,T3,A1,A2,T5,T6,T7,R] = compose_3_2_7(other, this)
    def compose4[A1,A2](other : Term2[A1,A2,T5]) : Term8[T1,T2,T3,T4,A1,A2,T6,T7,R] = compose_4_2_7(other, this)
    def compose5[A1,A2](other : Term2[A1,A2,T6]) : Term8[T1,T2,T3,T4,T5,A1,A2,T7,R] = compose_5_2_7(other, this)
    def compose6[A1,A2](other : Term2[A1,A2,T7]) : Term8[T1,T2,T3,T4,T5,T6,A1,A2,R] = compose_6_2_7(other, this)
    def compose0[A1,A2,A3](other : Term3[A1,A2,A3,T1]) : Term9[A1,A2,A3,T2,T3,T4,T5,T6,T7,R] = compose_0_3_7(other, this)
    def compose1[A1,A2,A3](other : Term3[A1,A2,A3,T2]) : Term9[T1,A1,A2,A3,T3,T4,T5,T6,T7,R] = compose_1_3_7(other, this)
    def compose2[A1,A2,A3](other : Term3[A1,A2,A3,T3]) : Term9[T1,T2,A1,A2,A3,T4,T5,T6,T7,R] = compose_2_3_7(other, this)
    def compose3[A1,A2,A3](other : Term3[A1,A2,A3,T4]) : Term9[T1,T2,T3,A1,A2,A3,T5,T6,T7,R] = compose_3_3_7(other, this)
    def compose4[A1,A2,A3](other : Term3[A1,A2,A3,T5]) : Term9[T1,T2,T3,T4,A1,A2,A3,T6,T7,R] = compose_4_3_7(other, this)
    def compose5[A1,A2,A3](other : Term3[A1,A2,A3,T6]) : Term9[T1,T2,T3,T4,T5,A1,A2,A3,T7,R] = compose_5_3_7(other, this)
    def compose6[A1,A2,A3](other : Term3[A1,A2,A3,T7]) : Term9[T1,T2,T3,T4,T5,T6,A1,A2,A3,R] = compose_6_3_7(other, this)
  }

  sealed trait Term8[T1,T2,T3,T4,T5,T6,T7,T8,R] extends Term[(T1,T2,T3,T4,T5,T6,T7,T8),R] {
    val convertingFunction = converterOf(this).exprSeq2scala8[T1,T2,T3,T4,T5,T6,T7,T8] _
    type t2c = (Term8[T1,T2,T3,T4,T5,T6,T7,T8,R]) => Term8[T1,T2,T3,T4,T5,T6,T7,T8,Boolean]
    
    def ||(other : Term8[T1,T2,T3,T4,T5,T6,T7,T8,Boolean])(implicit asConstraint : t2c) : Term8[T1,T2,T3,T4,T5,T6,T7,T8,Boolean] = OrConstraint8[T1,T2,T3,T4,T5,T6,T7,T8](this, other)

    def &&(other : Term8[T1,T2,T3,T4,T5,T6,T7,T8,Boolean])(implicit asConstraint : t2c) : Term8[T1,T2,T3,T4,T5,T6,T7,T8,Boolean] = AndConstraint8[T1,T2,T3,T4,T5,T6,T7,T8](this, other)

    def unary_!(implicit asConstraint : t2c) : Term8[T1,T2,T3,T4,T5,T6,T7,T8,Boolean] = NotConstraint8[T1,T2,T3,T4,T5,T6,T7,T8](this)

    def minimizing(minFunc : Term8[T1,T2,T3,T4,T5,T6,T7,T8,Int])(implicit asConstraint : t2c) : MinConstraint8[T1,T2,T3,T4,T5,T6,T7,T8] = {
      MinConstraint8[T1,T2,T3,T4,T5,T6,T7,T8](asConstraint(this), minFunc)
    }

    def compose0[A1](other : Term1[A1,T1]) : Term8[A1,T2,T3,T4,T5,T6,T7,T8,R] = compose_0_1_8(other, this)
    def compose1[A1](other : Term1[A1,T2]) : Term8[T1,A1,T3,T4,T5,T6,T7,T8,R] = compose_1_1_8(other, this)
    def compose2[A1](other : Term1[A1,T3]) : Term8[T1,T2,A1,T4,T5,T6,T7,T8,R] = compose_2_1_8(other, this)
    def compose3[A1](other : Term1[A1,T4]) : Term8[T1,T2,T3,A1,T5,T6,T7,T8,R] = compose_3_1_8(other, this)
    def compose4[A1](other : Term1[A1,T5]) : Term8[T1,T2,T3,T4,A1,T6,T7,T8,R] = compose_4_1_8(other, this)
    def compose5[A1](other : Term1[A1,T6]) : Term8[T1,T2,T3,T4,T5,A1,T7,T8,R] = compose_5_1_8(other, this)
    def compose6[A1](other : Term1[A1,T7]) : Term8[T1,T2,T3,T4,T5,T6,A1,T8,R] = compose_6_1_8(other, this)
    def compose7[A1](other : Term1[A1,T8]) : Term8[T1,T2,T3,T4,T5,T6,T7,A1,R] = compose_7_1_8(other, this)
    def compose0[A1,A2](other : Term2[A1,A2,T1]) : Term9[A1,A2,T2,T3,T4,T5,T6,T7,T8,R] = compose_0_2_8(other, this)
    def compose1[A1,A2](other : Term2[A1,A2,T2]) : Term9[T1,A1,A2,T3,T4,T5,T6,T7,T8,R] = compose_1_2_8(other, this)
    def compose2[A1,A2](other : Term2[A1,A2,T3]) : Term9[T1,T2,A1,A2,T4,T5,T6,T7,T8,R] = compose_2_2_8(other, this)
    def compose3[A1,A2](other : Term2[A1,A2,T4]) : Term9[T1,T2,T3,A1,A2,T5,T6,T7,T8,R] = compose_3_2_8(other, this)
    def compose4[A1,A2](other : Term2[A1,A2,T5]) : Term9[T1,T2,T3,T4,A1,A2,T6,T7,T8,R] = compose_4_2_8(other, this)
    def compose5[A1,A2](other : Term2[A1,A2,T6]) : Term9[T1,T2,T3,T4,T5,A1,A2,T7,T8,R] = compose_5_2_8(other, this)
    def compose6[A1,A2](other : Term2[A1,A2,T7]) : Term9[T1,T2,T3,T4,T5,T6,A1,A2,T8,R] = compose_6_2_8(other, this)
    def compose7[A1,A2](other : Term2[A1,A2,T8]) : Term9[T1,T2,T3,T4,T5,T6,T7,A1,A2,R] = compose_7_2_8(other, this)
  }

  sealed trait Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,R] extends Term[(T1,T2,T3,T4,T5,T6,T7,T8,T9),R] {
    val convertingFunction = converterOf(this).exprSeq2scala9[T1,T2,T3,T4,T5,T6,T7,T8,T9] _
    type t2c = (Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,R]) => Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,Boolean]
    
    def ||(other : Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,Boolean])(implicit asConstraint : t2c) : Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,Boolean] = OrConstraint9[T1,T2,T3,T4,T5,T6,T7,T8,T9](this, other)

    def &&(other : Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,Boolean])(implicit asConstraint : t2c) : Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,Boolean] = AndConstraint9[T1,T2,T3,T4,T5,T6,T7,T8,T9](this, other)

    def unary_!(implicit asConstraint : t2c) : Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,Boolean] = NotConstraint9[T1,T2,T3,T4,T5,T6,T7,T8,T9](this)

    def minimizing(minFunc : Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,Int])(implicit asConstraint : t2c) : MinConstraint9[T1,T2,T3,T4,T5,T6,T7,T8,T9] = {
      MinConstraint9[T1,T2,T3,T4,T5,T6,T7,T8,T9](asConstraint(this), minFunc)
    }

    def compose0[A1](other : Term1[A1,T1]) : Term9[A1,T2,T3,T4,T5,T6,T7,T8,T9,R] = compose_0_1_9(other, this)
    def compose1[A1](other : Term1[A1,T2]) : Term9[T1,A1,T3,T4,T5,T6,T7,T8,T9,R] = compose_1_1_9(other, this)
    def compose2[A1](other : Term1[A1,T3]) : Term9[T1,T2,A1,T4,T5,T6,T7,T8,T9,R] = compose_2_1_9(other, this)
    def compose3[A1](other : Term1[A1,T4]) : Term9[T1,T2,T3,A1,T5,T6,T7,T8,T9,R] = compose_3_1_9(other, this)
    def compose4[A1](other : Term1[A1,T5]) : Term9[T1,T2,T3,T4,A1,T6,T7,T8,T9,R] = compose_4_1_9(other, this)
    def compose5[A1](other : Term1[A1,T6]) : Term9[T1,T2,T3,T4,T5,A1,T7,T8,T9,R] = compose_5_1_9(other, this)
    def compose6[A1](other : Term1[A1,T7]) : Term9[T1,T2,T3,T4,T5,T6,A1,T8,T9,R] = compose_6_1_9(other, this)
    def compose7[A1](other : Term1[A1,T8]) : Term9[T1,T2,T3,T4,T5,T6,T7,A1,T9,R] = compose_7_1_9(other, this)
    def compose8[A1](other : Term1[A1,T9]) : Term9[T1,T2,T3,T4,T5,T6,T7,T8,A1,R] = compose_8_1_9(other, this)
  }

  object Term1 {
    def apply[T1,R](conv : Converter, serializedProg : Serialized, serializedInputVars: Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) = {
      val (converter, program, expr, types) = Term.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new Term[(T1),R](program, expr, types, converter) with Term1[T1,R]
    }
    
    def apply[T1,R](program : Program, expr : Expr, types : Seq[TypeTree], converter : Converter) =
      new Term[(T1),R](program, expr, types, converter) with Term1[T1,R]
  }

  object OrConstraint1 {
    def apply[T1](l : Term[(T1),Boolean], r : Term[(T1),Boolean]) : Term1[T1,Boolean] = (l, r) match {
      case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term1(p1,Or(ex1,ex2),ts1,conv1)
    }
  }

  object AndConstraint1 {
    def apply[T1](l : Term[(T1),Boolean], r : Term[(T1),Boolean]) : Term1[T1,Boolean] = (l, r) match {
      case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term1(p1,And(ex1,ex2),ts1,conv1)
    }
  }

  object NotConstraint1 {
    def apply[T1](c : Term[(T1),Boolean]) : Term1[T1,Boolean] = c match {
      case Term(p,ex,ts,conv) => Term1(p,Not(ex),ts,conv)
    }
  }

  object Term2 {
    def apply[T1,T2,R](conv : Converter, serializedProg : Serialized, serializedInputVars: Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) = {
      val (converter, program, expr, types) = Term.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new Term[(T1,T2),R](program, expr, types, converter) with Term2[T1,T2,R]
    }
    
    def apply[T1,T2,R](program : Program, expr : Expr, types : Seq[TypeTree], converter : Converter) =
      new Term[(T1,T2),R](program, expr, types, converter) with Term2[T1,T2,R]
  }

  object OrConstraint2 {
    def apply[T1,T2](l : Term[(T1,T2),Boolean], r : Term[(T1,T2),Boolean]) : Term2[T1,T2,Boolean] = (l, r) match {
      case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term2(p1,Or(ex1,ex2),ts1,conv1)
    }
  }

  object AndConstraint2 {
    def apply[T1,T2](l : Term[(T1,T2),Boolean], r : Term[(T1,T2),Boolean]) : Term2[T1,T2,Boolean] = (l, r) match {
      case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term2(p1,And(ex1,ex2),ts1,conv1)
    }
  }

  object NotConstraint2 {
    def apply[T1,T2](c : Term[(T1,T2),Boolean]) : Term2[T1,T2,Boolean] = c match {
      case Term(p,ex,ts,conv) => Term2(p,Not(ex),ts,conv)
    }
  }

  object Term3 {
    def apply[T1,T2,T3,R](conv : Converter, serializedProg : Serialized, serializedInputVars: Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) = {
      val (converter, program, expr, types) = Term.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new Term[(T1,T2,T3),R](program, expr, types, converter) with Term3[T1,T2,T3,R]
    }
    
    def apply[T1,T2,T3,R](program : Program, expr : Expr, types : Seq[TypeTree], converter : Converter) =
      new Term[(T1,T2,T3),R](program, expr, types, converter) with Term3[T1,T2,T3,R]
  }

  object OrConstraint3 {
    def apply[T1,T2,T3](l : Term[(T1,T2,T3),Boolean], r : Term[(T1,T2,T3),Boolean]) : Term3[T1,T2,T3,Boolean] = (l, r) match {
      case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term3(p1,Or(ex1,ex2),ts1,conv1)
    }
  }

  object AndConstraint3 {
    def apply[T1,T2,T3](l : Term[(T1,T2,T3),Boolean], r : Term[(T1,T2,T3),Boolean]) : Term3[T1,T2,T3,Boolean] = (l, r) match {
      case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term3(p1,And(ex1,ex2),ts1,conv1)
    }
  }

  object NotConstraint3 {
    def apply[T1,T2,T3](c : Term[(T1,T2,T3),Boolean]) : Term3[T1,T2,T3,Boolean] = c match {
      case Term(p,ex,ts,conv) => Term3(p,Not(ex),ts,conv)
    }
  }

  object Term4 {
    def apply[T1,T2,T3,T4,R](conv : Converter, serializedProg : Serialized, serializedInputVars: Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) = {
      val (converter, program, expr, types) = Term.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new Term[(T1,T2,T3,T4),R](program, expr, types, converter) with Term4[T1,T2,T3,T4,R]
    }
    
    def apply[T1,T2,T3,T4,R](program : Program, expr : Expr, types : Seq[TypeTree], converter : Converter) =
      new Term[(T1,T2,T3,T4),R](program, expr, types, converter) with Term4[T1,T2,T3,T4,R]
  }

  object OrConstraint4 {
    def apply[T1,T2,T3,T4](l : Term[(T1,T2,T3,T4),Boolean], r : Term[(T1,T2,T3,T4),Boolean]) : Term4[T1,T2,T3,T4,Boolean] = (l, r) match {
      case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term4(p1,Or(ex1,ex2),ts1,conv1)
    }
  }

  object AndConstraint4 {
    def apply[T1,T2,T3,T4](l : Term[(T1,T2,T3,T4),Boolean], r : Term[(T1,T2,T3,T4),Boolean]) : Term4[T1,T2,T3,T4,Boolean] = (l, r) match {
      case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term4(p1,And(ex1,ex2),ts1,conv1)
    }
  }

  object NotConstraint4 {
    def apply[T1,T2,T3,T4](c : Term[(T1,T2,T3,T4),Boolean]) : Term4[T1,T2,T3,T4,Boolean] = c match {
      case Term(p,ex,ts,conv) => Term4(p,Not(ex),ts,conv)
    }
  }

  object Term5 {
    def apply[T1,T2,T3,T4,T5,R](conv : Converter, serializedProg : Serialized, serializedInputVars: Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) = {
      val (converter, program, expr, types) = Term.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new Term[(T1,T2,T3,T4,T5),R](program, expr, types, converter) with Term5[T1,T2,T3,T4,T5,R]
    }
    
    def apply[T1,T2,T3,T4,T5,R](program : Program, expr : Expr, types : Seq[TypeTree], converter : Converter) =
      new Term[(T1,T2,T3,T4,T5),R](program, expr, types, converter) with Term5[T1,T2,T3,T4,T5,R]
  }

  object OrConstraint5 {
    def apply[T1,T2,T3,T4,T5](l : Term[(T1,T2,T3,T4,T5),Boolean], r : Term[(T1,T2,T3,T4,T5),Boolean]) : Term5[T1,T2,T3,T4,T5,Boolean] = (l, r) match {
      case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term5(p1,Or(ex1,ex2),ts1,conv1)
    }
  }

  object AndConstraint5 {
    def apply[T1,T2,T3,T4,T5](l : Term[(T1,T2,T3,T4,T5),Boolean], r : Term[(T1,T2,T3,T4,T5),Boolean]) : Term5[T1,T2,T3,T4,T5,Boolean] = (l, r) match {
      case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term5(p1,And(ex1,ex2),ts1,conv1)
    }
  }

  object NotConstraint5 {
    def apply[T1,T2,T3,T4,T5](c : Term[(T1,T2,T3,T4,T5),Boolean]) : Term5[T1,T2,T3,T4,T5,Boolean] = c match {
      case Term(p,ex,ts,conv) => Term5(p,Not(ex),ts,conv)
    }
  }

  object Term6 {
    def apply[T1,T2,T3,T4,T5,T6,R](conv : Converter, serializedProg : Serialized, serializedInputVars: Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) = {
      val (converter, program, expr, types) = Term.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new Term[(T1,T2,T3,T4,T5,T6),R](program, expr, types, converter) with Term6[T1,T2,T3,T4,T5,T6,R]
    }
    
    def apply[T1,T2,T3,T4,T5,T6,R](program : Program, expr : Expr, types : Seq[TypeTree], converter : Converter) =
      new Term[(T1,T2,T3,T4,T5,T6),R](program, expr, types, converter) with Term6[T1,T2,T3,T4,T5,T6,R]
  }

  object OrConstraint6 {
    def apply[T1,T2,T3,T4,T5,T6](l : Term[(T1,T2,T3,T4,T5,T6),Boolean], r : Term[(T1,T2,T3,T4,T5,T6),Boolean]) : Term6[T1,T2,T3,T4,T5,T6,Boolean] = (l, r) match {
      case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term6(p1,Or(ex1,ex2),ts1,conv1)
    }
  }

  object AndConstraint6 {
    def apply[T1,T2,T3,T4,T5,T6](l : Term[(T1,T2,T3,T4,T5,T6),Boolean], r : Term[(T1,T2,T3,T4,T5,T6),Boolean]) : Term6[T1,T2,T3,T4,T5,T6,Boolean] = (l, r) match {
      case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term6(p1,And(ex1,ex2),ts1,conv1)
    }
  }

  object NotConstraint6 {
    def apply[T1,T2,T3,T4,T5,T6](c : Term[(T1,T2,T3,T4,T5,T6),Boolean]) : Term6[T1,T2,T3,T4,T5,T6,Boolean] = c match {
      case Term(p,ex,ts,conv) => Term6(p,Not(ex),ts,conv)
    }
  }

  object Term7 {
    def apply[T1,T2,T3,T4,T5,T6,T7,R](conv : Converter, serializedProg : Serialized, serializedInputVars: Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) = {
      val (converter, program, expr, types) = Term.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new Term[(T1,T2,T3,T4,T5,T6,T7),R](program, expr, types, converter) with Term7[T1,T2,T3,T4,T5,T6,T7,R]
    }
    
    def apply[T1,T2,T3,T4,T5,T6,T7,R](program : Program, expr : Expr, types : Seq[TypeTree], converter : Converter) =
      new Term[(T1,T2,T3,T4,T5,T6,T7),R](program, expr, types, converter) with Term7[T1,T2,T3,T4,T5,T6,T7,R]
  }

  object OrConstraint7 {
    def apply[T1,T2,T3,T4,T5,T6,T7](l : Term[(T1,T2,T3,T4,T5,T6,T7),Boolean], r : Term[(T1,T2,T3,T4,T5,T6,T7),Boolean]) : Term7[T1,T2,T3,T4,T5,T6,T7,Boolean] = (l, r) match {
      case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term7(p1,Or(ex1,ex2),ts1,conv1)
    }
  }

  object AndConstraint7 {
    def apply[T1,T2,T3,T4,T5,T6,T7](l : Term[(T1,T2,T3,T4,T5,T6,T7),Boolean], r : Term[(T1,T2,T3,T4,T5,T6,T7),Boolean]) : Term7[T1,T2,T3,T4,T5,T6,T7,Boolean] = (l, r) match {
      case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term7(p1,And(ex1,ex2),ts1,conv1)
    }
  }

  object NotConstraint7 {
    def apply[T1,T2,T3,T4,T5,T6,T7](c : Term[(T1,T2,T3,T4,T5,T6,T7),Boolean]) : Term7[T1,T2,T3,T4,T5,T6,T7,Boolean] = c match {
      case Term(p,ex,ts,conv) => Term7(p,Not(ex),ts,conv)
    }
  }

  object Term8 {
    def apply[T1,T2,T3,T4,T5,T6,T7,T8,R](conv : Converter, serializedProg : Serialized, serializedInputVars: Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) = {
      val (converter, program, expr, types) = Term.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new Term[(T1,T2,T3,T4,T5,T6,T7,T8),R](program, expr, types, converter) with Term8[T1,T2,T3,T4,T5,T6,T7,T8,R]
    }
    
    def apply[T1,T2,T3,T4,T5,T6,T7,T8,R](program : Program, expr : Expr, types : Seq[TypeTree], converter : Converter) =
      new Term[(T1,T2,T3,T4,T5,T6,T7,T8),R](program, expr, types, converter) with Term8[T1,T2,T3,T4,T5,T6,T7,T8,R]
  }

  object OrConstraint8 {
    def apply[T1,T2,T3,T4,T5,T6,T7,T8](l : Term[(T1,T2,T3,T4,T5,T6,T7,T8),Boolean], r : Term[(T1,T2,T3,T4,T5,T6,T7,T8),Boolean]) : Term8[T1,T2,T3,T4,T5,T6,T7,T8,Boolean] = (l, r) match {
      case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term8(p1,Or(ex1,ex2),ts1,conv1)
    }
  }

  object AndConstraint8 {
    def apply[T1,T2,T3,T4,T5,T6,T7,T8](l : Term[(T1,T2,T3,T4,T5,T6,T7,T8),Boolean], r : Term[(T1,T2,T3,T4,T5,T6,T7,T8),Boolean]) : Term8[T1,T2,T3,T4,T5,T6,T7,T8,Boolean] = (l, r) match {
      case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term8(p1,And(ex1,ex2),ts1,conv1)
    }
  }

  object NotConstraint8 {
    def apply[T1,T2,T3,T4,T5,T6,T7,T8](c : Term[(T1,T2,T3,T4,T5,T6,T7,T8),Boolean]) : Term8[T1,T2,T3,T4,T5,T6,T7,T8,Boolean] = c match {
      case Term(p,ex,ts,conv) => Term8(p,Not(ex),ts,conv)
    }
  }

  object Term9 {
    def apply[T1,T2,T3,T4,T5,T6,T7,T8,T9,R](conv : Converter, serializedProg : Serialized, serializedInputVars: Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) = {
      val (converter, program, expr, types) = Term.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
      new Term[(T1,T2,T3,T4,T5,T6,T7,T8,T9),R](program, expr, types, converter) with Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,R]
    }
    
    def apply[T1,T2,T3,T4,T5,T6,T7,T8,T9,R](program : Program, expr : Expr, types : Seq[TypeTree], converter : Converter) =
      new Term[(T1,T2,T3,T4,T5,T6,T7,T8,T9),R](program, expr, types, converter) with Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,R]
  }

  object OrConstraint9 {
    def apply[T1,T2,T3,T4,T5,T6,T7,T8,T9](l : Term[(T1,T2,T3,T4,T5,T6,T7,T8,T9),Boolean], r : Term[(T1,T2,T3,T4,T5,T6,T7,T8,T9),Boolean]) : Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,Boolean] = (l, r) match {
      case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term9(p1,Or(ex1,ex2),ts1,conv1)
    }
  }

  object AndConstraint9 {
    def apply[T1,T2,T3,T4,T5,T6,T7,T8,T9](l : Term[(T1,T2,T3,T4,T5,T6,T7,T8,T9),Boolean], r : Term[(T1,T2,T3,T4,T5,T6,T7,T8,T9),Boolean]) : Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,Boolean] = (l, r) match {
      case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term9(p1,And(ex1,ex2),ts1,conv1)
    }
  }

  object NotConstraint9 {
    def apply[T1,T2,T3,T4,T5,T6,T7,T8,T9](c : Term[(T1,T2,T3,T4,T5,T6,T7,T8,T9),Boolean]) : Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,Boolean] = c match {
      case Term(p,ex,ts,conv) => Term9(p,Not(ex),ts,conv)
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

  /********** TERM METHODS **********/
  /** compose_i_j_k will compose f (of arity j) and g (of arity k) as "g∘f" by
   * inserting arguments of f in place of argument i of g */
  private def compose_0_1_1[A1,R1,R2](f : Term[(A1),R1], g : Term[(R1),R2]) : Term1[A1,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 1, 1)
    Term1(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_2_1[A1,A2,R1,R2](f : Term[(A1,A2),R1], g : Term[(R1),R2]) : Term2[A1,A2,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 2, 1)
    Term2(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_3_1[A1,A2,A3,R1,R2](f : Term[(A1,A2,A3),R1], g : Term[(R1),R2]) : Term3[A1,A2,A3,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 3, 1)
    Term3(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_4_1[A1,A2,A3,A4,R1,R2](f : Term[(A1,A2,A3,A4),R1], g : Term[(R1),R2]) : Term4[A1,A2,A3,A4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 4, 1)
    Term4(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_5_1[A1,A2,A3,A4,A5,R1,R2](f : Term[(A1,A2,A3,A4,A5),R1], g : Term[(R1),R2]) : Term5[A1,A2,A3,A4,A5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 5, 1)
    Term5(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_6_1[A1,A2,A3,A4,A5,A6,R1,R2](f : Term[(A1,A2,A3,A4,A5,A6),R1], g : Term[(R1),R2]) : Term6[A1,A2,A3,A4,A5,A6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 6, 1)
    Term6(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_7_1[A1,A2,A3,A4,A5,A6,A7,R1,R2](f : Term[(A1,A2,A3,A4,A5,A6,A7),R1], g : Term[(R1),R2]) : Term7[A1,A2,A3,A4,A5,A6,A7,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 7, 1)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_8_1[A1,A2,A3,A4,A5,A6,A7,A8,R1,R2](f : Term[(A1,A2,A3,A4,A5,A6,A7,A8),R1], g : Term[(R1),R2]) : Term8[A1,A2,A3,A4,A5,A6,A7,A8,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 8, 1)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_9_1[A1,A2,A3,A4,A5,A6,A7,A8,A9,R1,R2](f : Term[(A1,A2,A3,A4,A5,A6,A7,A8,A9),R1], g : Term[(R1),R2]) : Term9[A1,A2,A3,A4,A5,A6,A7,A8,A9,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 9, 1)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_1_2[A1,R1,B2,R2](f : Term[(A1),R1], g : Term[(R1,B2),R2]) : Term2[A1,B2,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 1, 2)
    Term2(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_1_2[A1,R1,B1,R2](f : Term[(A1),R1], g : Term[(B1,R1),R2]) : Term2[B1,A1,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 1, 2)
    Term2(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_2_2[A1,A2,R1,B2,R2](f : Term[(A1,A2),R1], g : Term[(R1,B2),R2]) : Term3[A1,A2,B2,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 2, 2)
    Term3(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_2_2[A1,A2,R1,B1,R2](f : Term[(A1,A2),R1], g : Term[(B1,R1),R2]) : Term3[B1,A1,A2,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 2, 2)
    Term3(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_3_2[A1,A2,A3,R1,B2,R2](f : Term[(A1,A2,A3),R1], g : Term[(R1,B2),R2]) : Term4[A1,A2,A3,B2,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 3, 2)
    Term4(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_3_2[A1,A2,A3,R1,B1,R2](f : Term[(A1,A2,A3),R1], g : Term[(B1,R1),R2]) : Term4[B1,A1,A2,A3,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 3, 2)
    Term4(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_4_2[A1,A2,A3,A4,R1,B2,R2](f : Term[(A1,A2,A3,A4),R1], g : Term[(R1,B2),R2]) : Term5[A1,A2,A3,A4,B2,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 4, 2)
    Term5(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_4_2[A1,A2,A3,A4,R1,B1,R2](f : Term[(A1,A2,A3,A4),R1], g : Term[(B1,R1),R2]) : Term5[B1,A1,A2,A3,A4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 4, 2)
    Term5(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_5_2[A1,A2,A3,A4,A5,R1,B2,R2](f : Term[(A1,A2,A3,A4,A5),R1], g : Term[(R1,B2),R2]) : Term6[A1,A2,A3,A4,A5,B2,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 5, 2)
    Term6(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_5_2[A1,A2,A3,A4,A5,R1,B1,R2](f : Term[(A1,A2,A3,A4,A5),R1], g : Term[(B1,R1),R2]) : Term6[B1,A1,A2,A3,A4,A5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 5, 2)
    Term6(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_6_2[A1,A2,A3,A4,A5,A6,R1,B2,R2](f : Term[(A1,A2,A3,A4,A5,A6),R1], g : Term[(R1,B2),R2]) : Term7[A1,A2,A3,A4,A5,A6,B2,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 6, 2)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_6_2[A1,A2,A3,A4,A5,A6,R1,B1,R2](f : Term[(A1,A2,A3,A4,A5,A6),R1], g : Term[(B1,R1),R2]) : Term7[B1,A1,A2,A3,A4,A5,A6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 6, 2)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_7_2[A1,A2,A3,A4,A5,A6,A7,R1,B2,R2](f : Term[(A1,A2,A3,A4,A5,A6,A7),R1], g : Term[(R1,B2),R2]) : Term8[A1,A2,A3,A4,A5,A6,A7,B2,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 7, 2)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_7_2[A1,A2,A3,A4,A5,A6,A7,R1,B1,R2](f : Term[(A1,A2,A3,A4,A5,A6,A7),R1], g : Term[(B1,R1),R2]) : Term8[B1,A1,A2,A3,A4,A5,A6,A7,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 7, 2)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_8_2[A1,A2,A3,A4,A5,A6,A7,A8,R1,B2,R2](f : Term[(A1,A2,A3,A4,A5,A6,A7,A8),R1], g : Term[(R1,B2),R2]) : Term9[A1,A2,A3,A4,A5,A6,A7,A8,B2,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 8, 2)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_8_2[A1,A2,A3,A4,A5,A6,A7,A8,R1,B1,R2](f : Term[(A1,A2,A3,A4,A5,A6,A7,A8),R1], g : Term[(B1,R1),R2]) : Term9[B1,A1,A2,A3,A4,A5,A6,A7,A8,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 8, 2)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_1_3[A1,R1,B2,B3,R2](f : Term[(A1),R1], g : Term[(R1,B2,B3),R2]) : Term3[A1,B2,B3,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 1, 3)
    Term3(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_1_3[A1,R1,B1,B3,R2](f : Term[(A1),R1], g : Term[(B1,R1,B3),R2]) : Term3[B1,A1,B3,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 1, 3)
    Term3(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_1_3[A1,R1,B1,B2,R2](f : Term[(A1),R1], g : Term[(B1,B2,R1),R2]) : Term3[B1,B2,A1,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 1, 3)
    Term3(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_2_3[A1,A2,R1,B2,B3,R2](f : Term[(A1,A2),R1], g : Term[(R1,B2,B3),R2]) : Term4[A1,A2,B2,B3,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 2, 3)
    Term4(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_2_3[A1,A2,R1,B1,B3,R2](f : Term[(A1,A2),R1], g : Term[(B1,R1,B3),R2]) : Term4[B1,A1,A2,B3,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 2, 3)
    Term4(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_2_3[A1,A2,R1,B1,B2,R2](f : Term[(A1,A2),R1], g : Term[(B1,B2,R1),R2]) : Term4[B1,B2,A1,A2,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 2, 3)
    Term4(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_3_3[A1,A2,A3,R1,B2,B3,R2](f : Term[(A1,A2,A3),R1], g : Term[(R1,B2,B3),R2]) : Term5[A1,A2,A3,B2,B3,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 3, 3)
    Term5(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_3_3[A1,A2,A3,R1,B1,B3,R2](f : Term[(A1,A2,A3),R1], g : Term[(B1,R1,B3),R2]) : Term5[B1,A1,A2,A3,B3,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 3, 3)
    Term5(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_3_3[A1,A2,A3,R1,B1,B2,R2](f : Term[(A1,A2,A3),R1], g : Term[(B1,B2,R1),R2]) : Term5[B1,B2,A1,A2,A3,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 3, 3)
    Term5(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_4_3[A1,A2,A3,A4,R1,B2,B3,R2](f : Term[(A1,A2,A3,A4),R1], g : Term[(R1,B2,B3),R2]) : Term6[A1,A2,A3,A4,B2,B3,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 4, 3)
    Term6(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_4_3[A1,A2,A3,A4,R1,B1,B3,R2](f : Term[(A1,A2,A3,A4),R1], g : Term[(B1,R1,B3),R2]) : Term6[B1,A1,A2,A3,A4,B3,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 4, 3)
    Term6(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_4_3[A1,A2,A3,A4,R1,B1,B2,R2](f : Term[(A1,A2,A3,A4),R1], g : Term[(B1,B2,R1),R2]) : Term6[B1,B2,A1,A2,A3,A4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 4, 3)
    Term6(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_5_3[A1,A2,A3,A4,A5,R1,B2,B3,R2](f : Term[(A1,A2,A3,A4,A5),R1], g : Term[(R1,B2,B3),R2]) : Term7[A1,A2,A3,A4,A5,B2,B3,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 5, 3)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_5_3[A1,A2,A3,A4,A5,R1,B1,B3,R2](f : Term[(A1,A2,A3,A4,A5),R1], g : Term[(B1,R1,B3),R2]) : Term7[B1,A1,A2,A3,A4,A5,B3,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 5, 3)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_5_3[A1,A2,A3,A4,A5,R1,B1,B2,R2](f : Term[(A1,A2,A3,A4,A5),R1], g : Term[(B1,B2,R1),R2]) : Term7[B1,B2,A1,A2,A3,A4,A5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 5, 3)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_6_3[A1,A2,A3,A4,A5,A6,R1,B2,B3,R2](f : Term[(A1,A2,A3,A4,A5,A6),R1], g : Term[(R1,B2,B3),R2]) : Term8[A1,A2,A3,A4,A5,A6,B2,B3,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 6, 3)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_6_3[A1,A2,A3,A4,A5,A6,R1,B1,B3,R2](f : Term[(A1,A2,A3,A4,A5,A6),R1], g : Term[(B1,R1,B3),R2]) : Term8[B1,A1,A2,A3,A4,A5,A6,B3,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 6, 3)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_6_3[A1,A2,A3,A4,A5,A6,R1,B1,B2,R2](f : Term[(A1,A2,A3,A4,A5,A6),R1], g : Term[(B1,B2,R1),R2]) : Term8[B1,B2,A1,A2,A3,A4,A5,A6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 6, 3)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_7_3[A1,A2,A3,A4,A5,A6,A7,R1,B2,B3,R2](f : Term[(A1,A2,A3,A4,A5,A6,A7),R1], g : Term[(R1,B2,B3),R2]) : Term9[A1,A2,A3,A4,A5,A6,A7,B2,B3,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 7, 3)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_7_3[A1,A2,A3,A4,A5,A6,A7,R1,B1,B3,R2](f : Term[(A1,A2,A3,A4,A5,A6,A7),R1], g : Term[(B1,R1,B3),R2]) : Term9[B1,A1,A2,A3,A4,A5,A6,A7,B3,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 7, 3)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_7_3[A1,A2,A3,A4,A5,A6,A7,R1,B1,B2,R2](f : Term[(A1,A2,A3,A4,A5,A6,A7),R1], g : Term[(B1,B2,R1),R2]) : Term9[B1,B2,A1,A2,A3,A4,A5,A6,A7,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 7, 3)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_1_4[A1,R1,B2,B3,B4,R2](f : Term[(A1),R1], g : Term[(R1,B2,B3,B4),R2]) : Term4[A1,B2,B3,B4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 1, 4)
    Term4(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_1_4[A1,R1,B1,B3,B4,R2](f : Term[(A1),R1], g : Term[(B1,R1,B3,B4),R2]) : Term4[B1,A1,B3,B4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 1, 4)
    Term4(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_1_4[A1,R1,B1,B2,B4,R2](f : Term[(A1),R1], g : Term[(B1,B2,R1,B4),R2]) : Term4[B1,B2,A1,B4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 1, 4)
    Term4(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_3_1_4[A1,R1,B1,B2,B3,R2](f : Term[(A1),R1], g : Term[(B1,B2,B3,R1),R2]) : Term4[B1,B2,B3,A1,R2] = {
    val (newExpr, newTypes) = compose(f, g, 3, 1, 4)
    Term4(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_2_4[A1,A2,R1,B2,B3,B4,R2](f : Term[(A1,A2),R1], g : Term[(R1,B2,B3,B4),R2]) : Term5[A1,A2,B2,B3,B4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 2, 4)
    Term5(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_2_4[A1,A2,R1,B1,B3,B4,R2](f : Term[(A1,A2),R1], g : Term[(B1,R1,B3,B4),R2]) : Term5[B1,A1,A2,B3,B4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 2, 4)
    Term5(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_2_4[A1,A2,R1,B1,B2,B4,R2](f : Term[(A1,A2),R1], g : Term[(B1,B2,R1,B4),R2]) : Term5[B1,B2,A1,A2,B4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 2, 4)
    Term5(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_3_2_4[A1,A2,R1,B1,B2,B3,R2](f : Term[(A1,A2),R1], g : Term[(B1,B2,B3,R1),R2]) : Term5[B1,B2,B3,A1,A2,R2] = {
    val (newExpr, newTypes) = compose(f, g, 3, 2, 4)
    Term5(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_3_4[A1,A2,A3,R1,B2,B3,B4,R2](f : Term[(A1,A2,A3),R1], g : Term[(R1,B2,B3,B4),R2]) : Term6[A1,A2,A3,B2,B3,B4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 3, 4)
    Term6(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_3_4[A1,A2,A3,R1,B1,B3,B4,R2](f : Term[(A1,A2,A3),R1], g : Term[(B1,R1,B3,B4),R2]) : Term6[B1,A1,A2,A3,B3,B4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 3, 4)
    Term6(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_3_4[A1,A2,A3,R1,B1,B2,B4,R2](f : Term[(A1,A2,A3),R1], g : Term[(B1,B2,R1,B4),R2]) : Term6[B1,B2,A1,A2,A3,B4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 3, 4)
    Term6(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_3_3_4[A1,A2,A3,R1,B1,B2,B3,R2](f : Term[(A1,A2,A3),R1], g : Term[(B1,B2,B3,R1),R2]) : Term6[B1,B2,B3,A1,A2,A3,R2] = {
    val (newExpr, newTypes) = compose(f, g, 3, 3, 4)
    Term6(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_4_4[A1,A2,A3,A4,R1,B2,B3,B4,R2](f : Term[(A1,A2,A3,A4),R1], g : Term[(R1,B2,B3,B4),R2]) : Term7[A1,A2,A3,A4,B2,B3,B4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 4, 4)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_4_4[A1,A2,A3,A4,R1,B1,B3,B4,R2](f : Term[(A1,A2,A3,A4),R1], g : Term[(B1,R1,B3,B4),R2]) : Term7[B1,A1,A2,A3,A4,B3,B4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 4, 4)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_4_4[A1,A2,A3,A4,R1,B1,B2,B4,R2](f : Term[(A1,A2,A3,A4),R1], g : Term[(B1,B2,R1,B4),R2]) : Term7[B1,B2,A1,A2,A3,A4,B4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 4, 4)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_3_4_4[A1,A2,A3,A4,R1,B1,B2,B3,R2](f : Term[(A1,A2,A3,A4),R1], g : Term[(B1,B2,B3,R1),R2]) : Term7[B1,B2,B3,A1,A2,A3,A4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 3, 4, 4)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_5_4[A1,A2,A3,A4,A5,R1,B2,B3,B4,R2](f : Term[(A1,A2,A3,A4,A5),R1], g : Term[(R1,B2,B3,B4),R2]) : Term8[A1,A2,A3,A4,A5,B2,B3,B4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 5, 4)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_5_4[A1,A2,A3,A4,A5,R1,B1,B3,B4,R2](f : Term[(A1,A2,A3,A4,A5),R1], g : Term[(B1,R1,B3,B4),R2]) : Term8[B1,A1,A2,A3,A4,A5,B3,B4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 5, 4)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_5_4[A1,A2,A3,A4,A5,R1,B1,B2,B4,R2](f : Term[(A1,A2,A3,A4,A5),R1], g : Term[(B1,B2,R1,B4),R2]) : Term8[B1,B2,A1,A2,A3,A4,A5,B4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 5, 4)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_3_5_4[A1,A2,A3,A4,A5,R1,B1,B2,B3,R2](f : Term[(A1,A2,A3,A4,A5),R1], g : Term[(B1,B2,B3,R1),R2]) : Term8[B1,B2,B3,A1,A2,A3,A4,A5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 3, 5, 4)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_6_4[A1,A2,A3,A4,A5,A6,R1,B2,B3,B4,R2](f : Term[(A1,A2,A3,A4,A5,A6),R1], g : Term[(R1,B2,B3,B4),R2]) : Term9[A1,A2,A3,A4,A5,A6,B2,B3,B4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 6, 4)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_6_4[A1,A2,A3,A4,A5,A6,R1,B1,B3,B4,R2](f : Term[(A1,A2,A3,A4,A5,A6),R1], g : Term[(B1,R1,B3,B4),R2]) : Term9[B1,A1,A2,A3,A4,A5,A6,B3,B4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 6, 4)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_6_4[A1,A2,A3,A4,A5,A6,R1,B1,B2,B4,R2](f : Term[(A1,A2,A3,A4,A5,A6),R1], g : Term[(B1,B2,R1,B4),R2]) : Term9[B1,B2,A1,A2,A3,A4,A5,A6,B4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 6, 4)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_3_6_4[A1,A2,A3,A4,A5,A6,R1,B1,B2,B3,R2](f : Term[(A1,A2,A3,A4,A5,A6),R1], g : Term[(B1,B2,B3,R1),R2]) : Term9[B1,B2,B3,A1,A2,A3,A4,A5,A6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 3, 6, 4)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_1_5[A1,R1,B2,B3,B4,B5,R2](f : Term[(A1),R1], g : Term[(R1,B2,B3,B4,B5),R2]) : Term5[A1,B2,B3,B4,B5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 1, 5)
    Term5(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_1_5[A1,R1,B1,B3,B4,B5,R2](f : Term[(A1),R1], g : Term[(B1,R1,B3,B4,B5),R2]) : Term5[B1,A1,B3,B4,B5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 1, 5)
    Term5(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_1_5[A1,R1,B1,B2,B4,B5,R2](f : Term[(A1),R1], g : Term[(B1,B2,R1,B4,B5),R2]) : Term5[B1,B2,A1,B4,B5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 1, 5)
    Term5(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_3_1_5[A1,R1,B1,B2,B3,B5,R2](f : Term[(A1),R1], g : Term[(B1,B2,B3,R1,B5),R2]) : Term5[B1,B2,B3,A1,B5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 3, 1, 5)
    Term5(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_4_1_5[A1,R1,B1,B2,B3,B4,R2](f : Term[(A1),R1], g : Term[(B1,B2,B3,B4,R1),R2]) : Term5[B1,B2,B3,B4,A1,R2] = {
    val (newExpr, newTypes) = compose(f, g, 4, 1, 5)
    Term5(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_2_5[A1,A2,R1,B2,B3,B4,B5,R2](f : Term[(A1,A2),R1], g : Term[(R1,B2,B3,B4,B5),R2]) : Term6[A1,A2,B2,B3,B4,B5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 2, 5)
    Term6(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_2_5[A1,A2,R1,B1,B3,B4,B5,R2](f : Term[(A1,A2),R1], g : Term[(B1,R1,B3,B4,B5),R2]) : Term6[B1,A1,A2,B3,B4,B5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 2, 5)
    Term6(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_2_5[A1,A2,R1,B1,B2,B4,B5,R2](f : Term[(A1,A2),R1], g : Term[(B1,B2,R1,B4,B5),R2]) : Term6[B1,B2,A1,A2,B4,B5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 2, 5)
    Term6(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_3_2_5[A1,A2,R1,B1,B2,B3,B5,R2](f : Term[(A1,A2),R1], g : Term[(B1,B2,B3,R1,B5),R2]) : Term6[B1,B2,B3,A1,A2,B5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 3, 2, 5)
    Term6(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_4_2_5[A1,A2,R1,B1,B2,B3,B4,R2](f : Term[(A1,A2),R1], g : Term[(B1,B2,B3,B4,R1),R2]) : Term6[B1,B2,B3,B4,A1,A2,R2] = {
    val (newExpr, newTypes) = compose(f, g, 4, 2, 5)
    Term6(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_3_5[A1,A2,A3,R1,B2,B3,B4,B5,R2](f : Term[(A1,A2,A3),R1], g : Term[(R1,B2,B3,B4,B5),R2]) : Term7[A1,A2,A3,B2,B3,B4,B5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 3, 5)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_3_5[A1,A2,A3,R1,B1,B3,B4,B5,R2](f : Term[(A1,A2,A3),R1], g : Term[(B1,R1,B3,B4,B5),R2]) : Term7[B1,A1,A2,A3,B3,B4,B5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 3, 5)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_3_5[A1,A2,A3,R1,B1,B2,B4,B5,R2](f : Term[(A1,A2,A3),R1], g : Term[(B1,B2,R1,B4,B5),R2]) : Term7[B1,B2,A1,A2,A3,B4,B5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 3, 5)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_3_3_5[A1,A2,A3,R1,B1,B2,B3,B5,R2](f : Term[(A1,A2,A3),R1], g : Term[(B1,B2,B3,R1,B5),R2]) : Term7[B1,B2,B3,A1,A2,A3,B5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 3, 3, 5)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_4_3_5[A1,A2,A3,R1,B1,B2,B3,B4,R2](f : Term[(A1,A2,A3),R1], g : Term[(B1,B2,B3,B4,R1),R2]) : Term7[B1,B2,B3,B4,A1,A2,A3,R2] = {
    val (newExpr, newTypes) = compose(f, g, 4, 3, 5)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_4_5[A1,A2,A3,A4,R1,B2,B3,B4,B5,R2](f : Term[(A1,A2,A3,A4),R1], g : Term[(R1,B2,B3,B4,B5),R2]) : Term8[A1,A2,A3,A4,B2,B3,B4,B5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 4, 5)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_4_5[A1,A2,A3,A4,R1,B1,B3,B4,B5,R2](f : Term[(A1,A2,A3,A4),R1], g : Term[(B1,R1,B3,B4,B5),R2]) : Term8[B1,A1,A2,A3,A4,B3,B4,B5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 4, 5)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_4_5[A1,A2,A3,A4,R1,B1,B2,B4,B5,R2](f : Term[(A1,A2,A3,A4),R1], g : Term[(B1,B2,R1,B4,B5),R2]) : Term8[B1,B2,A1,A2,A3,A4,B4,B5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 4, 5)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_3_4_5[A1,A2,A3,A4,R1,B1,B2,B3,B5,R2](f : Term[(A1,A2,A3,A4),R1], g : Term[(B1,B2,B3,R1,B5),R2]) : Term8[B1,B2,B3,A1,A2,A3,A4,B5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 3, 4, 5)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_4_4_5[A1,A2,A3,A4,R1,B1,B2,B3,B4,R2](f : Term[(A1,A2,A3,A4),R1], g : Term[(B1,B2,B3,B4,R1),R2]) : Term8[B1,B2,B3,B4,A1,A2,A3,A4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 4, 4, 5)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_5_5[A1,A2,A3,A4,A5,R1,B2,B3,B4,B5,R2](f : Term[(A1,A2,A3,A4,A5),R1], g : Term[(R1,B2,B3,B4,B5),R2]) : Term9[A1,A2,A3,A4,A5,B2,B3,B4,B5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 5, 5)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_5_5[A1,A2,A3,A4,A5,R1,B1,B3,B4,B5,R2](f : Term[(A1,A2,A3,A4,A5),R1], g : Term[(B1,R1,B3,B4,B5),R2]) : Term9[B1,A1,A2,A3,A4,A5,B3,B4,B5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 5, 5)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_5_5[A1,A2,A3,A4,A5,R1,B1,B2,B4,B5,R2](f : Term[(A1,A2,A3,A4,A5),R1], g : Term[(B1,B2,R1,B4,B5),R2]) : Term9[B1,B2,A1,A2,A3,A4,A5,B4,B5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 5, 5)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_3_5_5[A1,A2,A3,A4,A5,R1,B1,B2,B3,B5,R2](f : Term[(A1,A2,A3,A4,A5),R1], g : Term[(B1,B2,B3,R1,B5),R2]) : Term9[B1,B2,B3,A1,A2,A3,A4,A5,B5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 3, 5, 5)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_4_5_5[A1,A2,A3,A4,A5,R1,B1,B2,B3,B4,R2](f : Term[(A1,A2,A3,A4,A5),R1], g : Term[(B1,B2,B3,B4,R1),R2]) : Term9[B1,B2,B3,B4,A1,A2,A3,A4,A5,R2] = {
    val (newExpr, newTypes) = compose(f, g, 4, 5, 5)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_1_6[A1,R1,B2,B3,B4,B5,B6,R2](f : Term[(A1),R1], g : Term[(R1,B2,B3,B4,B5,B6),R2]) : Term6[A1,B2,B3,B4,B5,B6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 1, 6)
    Term6(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_1_6[A1,R1,B1,B3,B4,B5,B6,R2](f : Term[(A1),R1], g : Term[(B1,R1,B3,B4,B5,B6),R2]) : Term6[B1,A1,B3,B4,B5,B6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 1, 6)
    Term6(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_1_6[A1,R1,B1,B2,B4,B5,B6,R2](f : Term[(A1),R1], g : Term[(B1,B2,R1,B4,B5,B6),R2]) : Term6[B1,B2,A1,B4,B5,B6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 1, 6)
    Term6(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_3_1_6[A1,R1,B1,B2,B3,B5,B6,R2](f : Term[(A1),R1], g : Term[(B1,B2,B3,R1,B5,B6),R2]) : Term6[B1,B2,B3,A1,B5,B6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 3, 1, 6)
    Term6(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_4_1_6[A1,R1,B1,B2,B3,B4,B6,R2](f : Term[(A1),R1], g : Term[(B1,B2,B3,B4,R1,B6),R2]) : Term6[B1,B2,B3,B4,A1,B6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 4, 1, 6)
    Term6(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_5_1_6[A1,R1,B1,B2,B3,B4,B5,R2](f : Term[(A1),R1], g : Term[(B1,B2,B3,B4,B5,R1),R2]) : Term6[B1,B2,B3,B4,B5,A1,R2] = {
    val (newExpr, newTypes) = compose(f, g, 5, 1, 6)
    Term6(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_2_6[A1,A2,R1,B2,B3,B4,B5,B6,R2](f : Term[(A1,A2),R1], g : Term[(R1,B2,B3,B4,B5,B6),R2]) : Term7[A1,A2,B2,B3,B4,B5,B6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 2, 6)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_2_6[A1,A2,R1,B1,B3,B4,B5,B6,R2](f : Term[(A1,A2),R1], g : Term[(B1,R1,B3,B4,B5,B6),R2]) : Term7[B1,A1,A2,B3,B4,B5,B6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 2, 6)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_2_6[A1,A2,R1,B1,B2,B4,B5,B6,R2](f : Term[(A1,A2),R1], g : Term[(B1,B2,R1,B4,B5,B6),R2]) : Term7[B1,B2,A1,A2,B4,B5,B6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 2, 6)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_3_2_6[A1,A2,R1,B1,B2,B3,B5,B6,R2](f : Term[(A1,A2),R1], g : Term[(B1,B2,B3,R1,B5,B6),R2]) : Term7[B1,B2,B3,A1,A2,B5,B6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 3, 2, 6)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_4_2_6[A1,A2,R1,B1,B2,B3,B4,B6,R2](f : Term[(A1,A2),R1], g : Term[(B1,B2,B3,B4,R1,B6),R2]) : Term7[B1,B2,B3,B4,A1,A2,B6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 4, 2, 6)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_5_2_6[A1,A2,R1,B1,B2,B3,B4,B5,R2](f : Term[(A1,A2),R1], g : Term[(B1,B2,B3,B4,B5,R1),R2]) : Term7[B1,B2,B3,B4,B5,A1,A2,R2] = {
    val (newExpr, newTypes) = compose(f, g, 5, 2, 6)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_3_6[A1,A2,A3,R1,B2,B3,B4,B5,B6,R2](f : Term[(A1,A2,A3),R1], g : Term[(R1,B2,B3,B4,B5,B6),R2]) : Term8[A1,A2,A3,B2,B3,B4,B5,B6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 3, 6)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_3_6[A1,A2,A3,R1,B1,B3,B4,B5,B6,R2](f : Term[(A1,A2,A3),R1], g : Term[(B1,R1,B3,B4,B5,B6),R2]) : Term8[B1,A1,A2,A3,B3,B4,B5,B6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 3, 6)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_3_6[A1,A2,A3,R1,B1,B2,B4,B5,B6,R2](f : Term[(A1,A2,A3),R1], g : Term[(B1,B2,R1,B4,B5,B6),R2]) : Term8[B1,B2,A1,A2,A3,B4,B5,B6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 3, 6)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_3_3_6[A1,A2,A3,R1,B1,B2,B3,B5,B6,R2](f : Term[(A1,A2,A3),R1], g : Term[(B1,B2,B3,R1,B5,B6),R2]) : Term8[B1,B2,B3,A1,A2,A3,B5,B6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 3, 3, 6)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_4_3_6[A1,A2,A3,R1,B1,B2,B3,B4,B6,R2](f : Term[(A1,A2,A3),R1], g : Term[(B1,B2,B3,B4,R1,B6),R2]) : Term8[B1,B2,B3,B4,A1,A2,A3,B6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 4, 3, 6)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_5_3_6[A1,A2,A3,R1,B1,B2,B3,B4,B5,R2](f : Term[(A1,A2,A3),R1], g : Term[(B1,B2,B3,B4,B5,R1),R2]) : Term8[B1,B2,B3,B4,B5,A1,A2,A3,R2] = {
    val (newExpr, newTypes) = compose(f, g, 5, 3, 6)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_4_6[A1,A2,A3,A4,R1,B2,B3,B4,B5,B6,R2](f : Term[(A1,A2,A3,A4),R1], g : Term[(R1,B2,B3,B4,B5,B6),R2]) : Term9[A1,A2,A3,A4,B2,B3,B4,B5,B6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 4, 6)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_4_6[A1,A2,A3,A4,R1,B1,B3,B4,B5,B6,R2](f : Term[(A1,A2,A3,A4),R1], g : Term[(B1,R1,B3,B4,B5,B6),R2]) : Term9[B1,A1,A2,A3,A4,B3,B4,B5,B6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 4, 6)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_4_6[A1,A2,A3,A4,R1,B1,B2,B4,B5,B6,R2](f : Term[(A1,A2,A3,A4),R1], g : Term[(B1,B2,R1,B4,B5,B6),R2]) : Term9[B1,B2,A1,A2,A3,A4,B4,B5,B6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 4, 6)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_3_4_6[A1,A2,A3,A4,R1,B1,B2,B3,B5,B6,R2](f : Term[(A1,A2,A3,A4),R1], g : Term[(B1,B2,B3,R1,B5,B6),R2]) : Term9[B1,B2,B3,A1,A2,A3,A4,B5,B6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 3, 4, 6)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_4_4_6[A1,A2,A3,A4,R1,B1,B2,B3,B4,B6,R2](f : Term[(A1,A2,A3,A4),R1], g : Term[(B1,B2,B3,B4,R1,B6),R2]) : Term9[B1,B2,B3,B4,A1,A2,A3,A4,B6,R2] = {
    val (newExpr, newTypes) = compose(f, g, 4, 4, 6)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_5_4_6[A1,A2,A3,A4,R1,B1,B2,B3,B4,B5,R2](f : Term[(A1,A2,A3,A4),R1], g : Term[(B1,B2,B3,B4,B5,R1),R2]) : Term9[B1,B2,B3,B4,B5,A1,A2,A3,A4,R2] = {
    val (newExpr, newTypes) = compose(f, g, 5, 4, 6)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_1_7[A1,R1,B2,B3,B4,B5,B6,B7,R2](f : Term[(A1),R1], g : Term[(R1,B2,B3,B4,B5,B6,B7),R2]) : Term7[A1,B2,B3,B4,B5,B6,B7,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 1, 7)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_1_7[A1,R1,B1,B3,B4,B5,B6,B7,R2](f : Term[(A1),R1], g : Term[(B1,R1,B3,B4,B5,B6,B7),R2]) : Term7[B1,A1,B3,B4,B5,B6,B7,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 1, 7)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_1_7[A1,R1,B1,B2,B4,B5,B6,B7,R2](f : Term[(A1),R1], g : Term[(B1,B2,R1,B4,B5,B6,B7),R2]) : Term7[B1,B2,A1,B4,B5,B6,B7,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 1, 7)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_3_1_7[A1,R1,B1,B2,B3,B5,B6,B7,R2](f : Term[(A1),R1], g : Term[(B1,B2,B3,R1,B5,B6,B7),R2]) : Term7[B1,B2,B3,A1,B5,B6,B7,R2] = {
    val (newExpr, newTypes) = compose(f, g, 3, 1, 7)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_4_1_7[A1,R1,B1,B2,B3,B4,B6,B7,R2](f : Term[(A1),R1], g : Term[(B1,B2,B3,B4,R1,B6,B7),R2]) : Term7[B1,B2,B3,B4,A1,B6,B7,R2] = {
    val (newExpr, newTypes) = compose(f, g, 4, 1, 7)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_5_1_7[A1,R1,B1,B2,B3,B4,B5,B7,R2](f : Term[(A1),R1], g : Term[(B1,B2,B3,B4,B5,R1,B7),R2]) : Term7[B1,B2,B3,B4,B5,A1,B7,R2] = {
    val (newExpr, newTypes) = compose(f, g, 5, 1, 7)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_6_1_7[A1,R1,B1,B2,B3,B4,B5,B6,R2](f : Term[(A1),R1], g : Term[(B1,B2,B3,B4,B5,B6,R1),R2]) : Term7[B1,B2,B3,B4,B5,B6,A1,R2] = {
    val (newExpr, newTypes) = compose(f, g, 6, 1, 7)
    Term7(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_2_7[A1,A2,R1,B2,B3,B4,B5,B6,B7,R2](f : Term[(A1,A2),R1], g : Term[(R1,B2,B3,B4,B5,B6,B7),R2]) : Term8[A1,A2,B2,B3,B4,B5,B6,B7,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 2, 7)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_2_7[A1,A2,R1,B1,B3,B4,B5,B6,B7,R2](f : Term[(A1,A2),R1], g : Term[(B1,R1,B3,B4,B5,B6,B7),R2]) : Term8[B1,A1,A2,B3,B4,B5,B6,B7,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 2, 7)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_2_7[A1,A2,R1,B1,B2,B4,B5,B6,B7,R2](f : Term[(A1,A2),R1], g : Term[(B1,B2,R1,B4,B5,B6,B7),R2]) : Term8[B1,B2,A1,A2,B4,B5,B6,B7,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 2, 7)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_3_2_7[A1,A2,R1,B1,B2,B3,B5,B6,B7,R2](f : Term[(A1,A2),R1], g : Term[(B1,B2,B3,R1,B5,B6,B7),R2]) : Term8[B1,B2,B3,A1,A2,B5,B6,B7,R2] = {
    val (newExpr, newTypes) = compose(f, g, 3, 2, 7)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_4_2_7[A1,A2,R1,B1,B2,B3,B4,B6,B7,R2](f : Term[(A1,A2),R1], g : Term[(B1,B2,B3,B4,R1,B6,B7),R2]) : Term8[B1,B2,B3,B4,A1,A2,B6,B7,R2] = {
    val (newExpr, newTypes) = compose(f, g, 4, 2, 7)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_5_2_7[A1,A2,R1,B1,B2,B3,B4,B5,B7,R2](f : Term[(A1,A2),R1], g : Term[(B1,B2,B3,B4,B5,R1,B7),R2]) : Term8[B1,B2,B3,B4,B5,A1,A2,B7,R2] = {
    val (newExpr, newTypes) = compose(f, g, 5, 2, 7)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_6_2_7[A1,A2,R1,B1,B2,B3,B4,B5,B6,R2](f : Term[(A1,A2),R1], g : Term[(B1,B2,B3,B4,B5,B6,R1),R2]) : Term8[B1,B2,B3,B4,B5,B6,A1,A2,R2] = {
    val (newExpr, newTypes) = compose(f, g, 6, 2, 7)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_3_7[A1,A2,A3,R1,B2,B3,B4,B5,B6,B7,R2](f : Term[(A1,A2,A3),R1], g : Term[(R1,B2,B3,B4,B5,B6,B7),R2]) : Term9[A1,A2,A3,B2,B3,B4,B5,B6,B7,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 3, 7)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_3_7[A1,A2,A3,R1,B1,B3,B4,B5,B6,B7,R2](f : Term[(A1,A2,A3),R1], g : Term[(B1,R1,B3,B4,B5,B6,B7),R2]) : Term9[B1,A1,A2,A3,B3,B4,B5,B6,B7,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 3, 7)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_3_7[A1,A2,A3,R1,B1,B2,B4,B5,B6,B7,R2](f : Term[(A1,A2,A3),R1], g : Term[(B1,B2,R1,B4,B5,B6,B7),R2]) : Term9[B1,B2,A1,A2,A3,B4,B5,B6,B7,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 3, 7)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_3_3_7[A1,A2,A3,R1,B1,B2,B3,B5,B6,B7,R2](f : Term[(A1,A2,A3),R1], g : Term[(B1,B2,B3,R1,B5,B6,B7),R2]) : Term9[B1,B2,B3,A1,A2,A3,B5,B6,B7,R2] = {
    val (newExpr, newTypes) = compose(f, g, 3, 3, 7)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_4_3_7[A1,A2,A3,R1,B1,B2,B3,B4,B6,B7,R2](f : Term[(A1,A2,A3),R1], g : Term[(B1,B2,B3,B4,R1,B6,B7),R2]) : Term9[B1,B2,B3,B4,A1,A2,A3,B6,B7,R2] = {
    val (newExpr, newTypes) = compose(f, g, 4, 3, 7)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_5_3_7[A1,A2,A3,R1,B1,B2,B3,B4,B5,B7,R2](f : Term[(A1,A2,A3),R1], g : Term[(B1,B2,B3,B4,B5,R1,B7),R2]) : Term9[B1,B2,B3,B4,B5,A1,A2,A3,B7,R2] = {
    val (newExpr, newTypes) = compose(f, g, 5, 3, 7)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_6_3_7[A1,A2,A3,R1,B1,B2,B3,B4,B5,B6,R2](f : Term[(A1,A2,A3),R1], g : Term[(B1,B2,B3,B4,B5,B6,R1),R2]) : Term9[B1,B2,B3,B4,B5,B6,A1,A2,A3,R2] = {
    val (newExpr, newTypes) = compose(f, g, 6, 3, 7)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_1_8[A1,R1,B2,B3,B4,B5,B6,B7,B8,R2](f : Term[(A1),R1], g : Term[(R1,B2,B3,B4,B5,B6,B7,B8),R2]) : Term8[A1,B2,B3,B4,B5,B6,B7,B8,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 1, 8)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_1_8[A1,R1,B1,B3,B4,B5,B6,B7,B8,R2](f : Term[(A1),R1], g : Term[(B1,R1,B3,B4,B5,B6,B7,B8),R2]) : Term8[B1,A1,B3,B4,B5,B6,B7,B8,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 1, 8)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_1_8[A1,R1,B1,B2,B4,B5,B6,B7,B8,R2](f : Term[(A1),R1], g : Term[(B1,B2,R1,B4,B5,B6,B7,B8),R2]) : Term8[B1,B2,A1,B4,B5,B6,B7,B8,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 1, 8)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_3_1_8[A1,R1,B1,B2,B3,B5,B6,B7,B8,R2](f : Term[(A1),R1], g : Term[(B1,B2,B3,R1,B5,B6,B7,B8),R2]) : Term8[B1,B2,B3,A1,B5,B6,B7,B8,R2] = {
    val (newExpr, newTypes) = compose(f, g, 3, 1, 8)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_4_1_8[A1,R1,B1,B2,B3,B4,B6,B7,B8,R2](f : Term[(A1),R1], g : Term[(B1,B2,B3,B4,R1,B6,B7,B8),R2]) : Term8[B1,B2,B3,B4,A1,B6,B7,B8,R2] = {
    val (newExpr, newTypes) = compose(f, g, 4, 1, 8)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_5_1_8[A1,R1,B1,B2,B3,B4,B5,B7,B8,R2](f : Term[(A1),R1], g : Term[(B1,B2,B3,B4,B5,R1,B7,B8),R2]) : Term8[B1,B2,B3,B4,B5,A1,B7,B8,R2] = {
    val (newExpr, newTypes) = compose(f, g, 5, 1, 8)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_6_1_8[A1,R1,B1,B2,B3,B4,B5,B6,B8,R2](f : Term[(A1),R1], g : Term[(B1,B2,B3,B4,B5,B6,R1,B8),R2]) : Term8[B1,B2,B3,B4,B5,B6,A1,B8,R2] = {
    val (newExpr, newTypes) = compose(f, g, 6, 1, 8)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_7_1_8[A1,R1,B1,B2,B3,B4,B5,B6,B7,R2](f : Term[(A1),R1], g : Term[(B1,B2,B3,B4,B5,B6,B7,R1),R2]) : Term8[B1,B2,B3,B4,B5,B6,B7,A1,R2] = {
    val (newExpr, newTypes) = compose(f, g, 7, 1, 8)
    Term8(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_2_8[A1,A2,R1,B2,B3,B4,B5,B6,B7,B8,R2](f : Term[(A1,A2),R1], g : Term[(R1,B2,B3,B4,B5,B6,B7,B8),R2]) : Term9[A1,A2,B2,B3,B4,B5,B6,B7,B8,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 2, 8)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_2_8[A1,A2,R1,B1,B3,B4,B5,B6,B7,B8,R2](f : Term[(A1,A2),R1], g : Term[(B1,R1,B3,B4,B5,B6,B7,B8),R2]) : Term9[B1,A1,A2,B3,B4,B5,B6,B7,B8,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 2, 8)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_2_8[A1,A2,R1,B1,B2,B4,B5,B6,B7,B8,R2](f : Term[(A1,A2),R1], g : Term[(B1,B2,R1,B4,B5,B6,B7,B8),R2]) : Term9[B1,B2,A1,A2,B4,B5,B6,B7,B8,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 2, 8)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_3_2_8[A1,A2,R1,B1,B2,B3,B5,B6,B7,B8,R2](f : Term[(A1,A2),R1], g : Term[(B1,B2,B3,R1,B5,B6,B7,B8),R2]) : Term9[B1,B2,B3,A1,A2,B5,B6,B7,B8,R2] = {
    val (newExpr, newTypes) = compose(f, g, 3, 2, 8)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_4_2_8[A1,A2,R1,B1,B2,B3,B4,B6,B7,B8,R2](f : Term[(A1,A2),R1], g : Term[(B1,B2,B3,B4,R1,B6,B7,B8),R2]) : Term9[B1,B2,B3,B4,A1,A2,B6,B7,B8,R2] = {
    val (newExpr, newTypes) = compose(f, g, 4, 2, 8)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_5_2_8[A1,A2,R1,B1,B2,B3,B4,B5,B7,B8,R2](f : Term[(A1,A2),R1], g : Term[(B1,B2,B3,B4,B5,R1,B7,B8),R2]) : Term9[B1,B2,B3,B4,B5,A1,A2,B7,B8,R2] = {
    val (newExpr, newTypes) = compose(f, g, 5, 2, 8)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_6_2_8[A1,A2,R1,B1,B2,B3,B4,B5,B6,B8,R2](f : Term[(A1,A2),R1], g : Term[(B1,B2,B3,B4,B5,B6,R1,B8),R2]) : Term9[B1,B2,B3,B4,B5,B6,A1,A2,B8,R2] = {
    val (newExpr, newTypes) = compose(f, g, 6, 2, 8)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_7_2_8[A1,A2,R1,B1,B2,B3,B4,B5,B6,B7,R2](f : Term[(A1,A2),R1], g : Term[(B1,B2,B3,B4,B5,B6,B7,R1),R2]) : Term9[B1,B2,B3,B4,B5,B6,B7,A1,A2,R2] = {
    val (newExpr, newTypes) = compose(f, g, 7, 2, 8)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_0_1_9[A1,R1,B2,B3,B4,B5,B6,B7,B8,B9,R2](f : Term[(A1),R1], g : Term[(R1,B2,B3,B4,B5,B6,B7,B8,B9),R2]) : Term9[A1,B2,B3,B4,B5,B6,B7,B8,B9,R2] = {
    val (newExpr, newTypes) = compose(f, g, 0, 1, 9)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_1_1_9[A1,R1,B1,B3,B4,B5,B6,B7,B8,B9,R2](f : Term[(A1),R1], g : Term[(B1,R1,B3,B4,B5,B6,B7,B8,B9),R2]) : Term9[B1,A1,B3,B4,B5,B6,B7,B8,B9,R2] = {
    val (newExpr, newTypes) = compose(f, g, 1, 1, 9)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_2_1_9[A1,R1,B1,B2,B4,B5,B6,B7,B8,B9,R2](f : Term[(A1),R1], g : Term[(B1,B2,R1,B4,B5,B6,B7,B8,B9),R2]) : Term9[B1,B2,A1,B4,B5,B6,B7,B8,B9,R2] = {
    val (newExpr, newTypes) = compose(f, g, 2, 1, 9)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_3_1_9[A1,R1,B1,B2,B3,B5,B6,B7,B8,B9,R2](f : Term[(A1),R1], g : Term[(B1,B2,B3,R1,B5,B6,B7,B8,B9),R2]) : Term9[B1,B2,B3,A1,B5,B6,B7,B8,B9,R2] = {
    val (newExpr, newTypes) = compose(f, g, 3, 1, 9)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_4_1_9[A1,R1,B1,B2,B3,B4,B6,B7,B8,B9,R2](f : Term[(A1),R1], g : Term[(B1,B2,B3,B4,R1,B6,B7,B8,B9),R2]) : Term9[B1,B2,B3,B4,A1,B6,B7,B8,B9,R2] = {
    val (newExpr, newTypes) = compose(f, g, 4, 1, 9)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_5_1_9[A1,R1,B1,B2,B3,B4,B5,B7,B8,B9,R2](f : Term[(A1),R1], g : Term[(B1,B2,B3,B4,B5,R1,B7,B8,B9),R2]) : Term9[B1,B2,B3,B4,B5,A1,B7,B8,B9,R2] = {
    val (newExpr, newTypes) = compose(f, g, 5, 1, 9)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_6_1_9[A1,R1,B1,B2,B3,B4,B5,B6,B8,B9,R2](f : Term[(A1),R1], g : Term[(B1,B2,B3,B4,B5,B6,R1,B8,B9),R2]) : Term9[B1,B2,B3,B4,B5,B6,A1,B8,B9,R2] = {
    val (newExpr, newTypes) = compose(f, g, 6, 1, 9)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_7_1_9[A1,R1,B1,B2,B3,B4,B5,B6,B7,B9,R2](f : Term[(A1),R1], g : Term[(B1,B2,B3,B4,B5,B6,B7,R1,B9),R2]) : Term9[B1,B2,B3,B4,B5,B6,B7,A1,B9,R2] = {
    val (newExpr, newTypes) = compose(f, g, 7, 1, 9)
    Term9(f.program, newExpr, newTypes, f.converter)
  }

  private def compose_8_1_9[A1,R1,B1,B2,B3,B4,B5,B6,B7,B8,R2](f : Term[(A1),R1], g : Term[(B1,B2,B3,B4,B5,B6,B7,B8,R1),R2]) : Term9[B1,B2,B3,B4,B5,B6,B7,B8,A1,R2] = {
    val (newExpr, newTypes) = compose(f, g, 8, 1, 9)
    Term9(f.program, newExpr, newTypes, f.converter)
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
      val newTypes  = g.types.take(index) ++ f.types ++ g.types.drop(index + 1)
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
