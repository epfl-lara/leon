/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test.purescala

import leon.test._
import leon.purescala.Common._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.purescala.ExprOps._

class TreeOpsTests extends LeonTestSuite with WithLikelyEq {
  
  test("Path-aware simplifications") {
    // TODO actually testing something here would be better, sorry
    // PS

    assert(true)
  }

  /**
   * If the formula consist of some top level AND, find a top level
   * Equals and extract it, return the remaining formula as well
   */
  def extractEquals(expr: Expr): (Option[Equals], Expr) = expr match {
    case And(es) =>
      // OK now I'm just messing with you.
      val (r, nes) = es.foldLeft[(Option[Equals],Seq[Expr])]((None, Seq())) {
        case ((None, nes), eq @ Equals(_,_)) => (Some(eq), nes)
        case ((o, nes), e) => (o, e +: nes)
      }
      (r, And(nes.reverse))

    case e => (None, e)
  }


  def i(x: Int) = InfiniteIntegerLiteral(x)

  val xId = FreshIdentifier("x", IntegerType)
  val x = Variable(xId)
  val yId = FreshIdentifier("y", IntegerType)
  val y = Variable(yId)
  val xs = Set(xId, yId)

  val aId = FreshIdentifier("a", IntegerType)
  val a = Variable(aId)
  val bId = FreshIdentifier("b", IntegerType)
  val b = Variable(bId)
  val as = Set(aId, bId)

  def checkSameExpr(e1: Expr, e2: Expr, vs: Set[Identifier]) {
    assert( //this outer assert should not be needed because of the nested one
      LikelyEq(e1, e2, vs, BooleanLiteral(true), (e1, e2) => {assert(e1 === e2); true})
    )
  }

  test("simplifyArithmetic") {
    val e1 = Plus(InfiniteIntegerLiteral(3), InfiniteIntegerLiteral(2))
    checkSameExpr(e1, simplifyArithmetic(e1), Set())
    val e2 = Plus(x, Plus(InfiniteIntegerLiteral(3), InfiniteIntegerLiteral(2)))
    checkSameExpr(e2, simplifyArithmetic(e2), Set(xId))

    val e3 = Minus(InfiniteIntegerLiteral(3), InfiniteIntegerLiteral(2))
    checkSameExpr(e3, simplifyArithmetic(e3), Set())
    val e4 = Plus(x, Minus(InfiniteIntegerLiteral(3), InfiniteIntegerLiteral(2)))
    checkSameExpr(e4, simplifyArithmetic(e4), Set(xId))
    val e5 = Plus(x, Minus(x, InfiniteIntegerLiteral(2)))
    checkSameExpr(e5, simplifyArithmetic(e5), Set(xId))

    val e6 = Times(InfiniteIntegerLiteral(9), Plus(Division(x, InfiniteIntegerLiteral(3)), Division(x, InfiniteIntegerLiteral(6))))
    checkSameExpr(e6, simplifyArithmetic(e6), Set(xId))
  }

  test("expandAndSimplifyArithmetic") {
    val e1 = Plus(InfiniteIntegerLiteral(3), InfiniteIntegerLiteral(2))
    checkSameExpr(e1, expandAndSimplifyArithmetic(e1), Set())
    val e2 = Plus(x, Plus(InfiniteIntegerLiteral(3), InfiniteIntegerLiteral(2)))
    checkSameExpr(e2, expandAndSimplifyArithmetic(e2), Set(xId))

    val e3 = Minus(InfiniteIntegerLiteral(3), InfiniteIntegerLiteral(2))
    checkSameExpr(e3, expandAndSimplifyArithmetic(e3), Set())
    val e4 = Plus(x, Minus(InfiniteIntegerLiteral(3), InfiniteIntegerLiteral(2)))
    checkSameExpr(e4, expandAndSimplifyArithmetic(e4), Set(xId))
    val e5 = Plus(x, Minus(x, InfiniteIntegerLiteral(2)))
    checkSameExpr(e5, expandAndSimplifyArithmetic(e5), Set(xId))

    val e6 = Times(InfiniteIntegerLiteral(9), Plus(Division(x, InfiniteIntegerLiteral(3)), Division(x, InfiniteIntegerLiteral(6))))
    checkSameExpr(e6, expandAndSimplifyArithmetic(e6), Set(xId))
  }

  test("extractEquals") {
    val eq = Equals(a, b)
    val lt1 = LessThan(a, b)
    val lt2 = LessThan(b, a)
    val lt3 = LessThan(x, y)

    val f1 = And(Seq(eq, lt1, lt2, lt3))
    val (eq1, r1) = extractEquals(f1)
    assert(eq1 != None)
    assert(eq1.get === eq)
    assert(extractEquals(r1)._1 === None)

    val f2 = And(Seq(lt1, lt2, eq, lt3))
    val (eq2, r2) = extractEquals(f2)
    assert(eq2 != None)
    assert(eq2.get === eq)
    assert(extractEquals(r2)._1 === None)

    val f3 = And(Seq(lt1, eq, lt2, lt3, eq))
    val (eq3, r3) = extractEquals(f3)
    assert(eq3 != None)
    assert(eq3.get === eq)
    val (eq4, r4) = extractEquals(r3)
    assert(eq4 != None)
    assert(eq4.get === eq)
    assert(extractEquals(r4)._1 === None)
  }

  test("pre and post traversal") {
    val expr = Plus(InfiniteIntegerLiteral(1), Minus(InfiniteIntegerLiteral(2), InfiniteIntegerLiteral(3)))
    var res = ""
    def f(e: Expr): Unit = e match {
      case InfiniteIntegerLiteral(i) => res += i
      case _ : Plus      => res += "P"
      case _ : Minus     => res += "M"
    }

    preTraversal(f)(expr)
    assert(res === "P1M23")

    res = ""
    postTraversal(f)(expr)
    assert(res === "123MP")
  }

  test("pre- and postMap") {
    val expr = Plus(InfiniteIntegerLiteral(1), Minus(InfiniteIntegerLiteral(2), InfiniteIntegerLiteral(3)))
    def op(e : Expr ) = e match {
      case Minus(InfiniteIntegerLiteral(two), e2) if two == BigInt(2) => Some(InfiniteIntegerLiteral(2))
      case InfiniteIntegerLiteral(one) if one == BigInt(1) => Some(InfiniteIntegerLiteral(2))
      case InfiniteIntegerLiteral(two) if two == BigInt(2) => Some(InfiniteIntegerLiteral(42))
      case _ => None
    }
    
    assert( preMap(op, false)(expr) == Plus(InfiniteIntegerLiteral(2),  InfiniteIntegerLiteral(2))  )
    assert( preMap(op, true )(expr) == Plus(InfiniteIntegerLiteral(42), InfiniteIntegerLiteral(42)) )
    assert( postMap(op, false)(expr) == Plus(InfiniteIntegerLiteral(2),  Minus(InfiniteIntegerLiteral(42), InfiniteIntegerLiteral(3))) )
    assert( postMap(op, true)(expr)  == Plus(InfiniteIntegerLiteral(42), Minus(InfiniteIntegerLiteral(42), InfiniteIntegerLiteral(3))) )
    
  }
  
}
