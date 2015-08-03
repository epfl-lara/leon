/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test.purescala

import leon.test._
import leon.purescala.Common._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.purescala.ExprOps._

class ExprOpsSuite extends LeonTestSuite with helpers.WithLikelyEq with helpers.ExpressionsDSL {

  private def foldConcatNames(e: Expr, subNames: Seq[String]): String = e match {
    case Variable(id) => subNames.mkString + id.name
    case _ => subNames.mkString
  }
  private def foldCountVariables(e: Expr, subCounts: Seq[Int]): Int = e match {
    case Variable(_) => subCounts.sum + 1
    case _ => subCounts.sum
  }

  test("foldRight works on single variable expression") { ctx =>
    assert(foldRight(foldConcatNames)(x) === x.id.name)
    assert(foldRight(foldConcatNames)(y) === y.id.name)
    assert(foldRight(foldCountVariables)(x) === 1)
    assert(foldRight(foldCountVariables)(y) === 1)
  }

  test("foldRight works on simple expressions without nested structure") { ctx =>
    assert(foldRight(foldConcatNames)(And(p, q)) === (p.id.name + q.id.name))
    assert(foldRight(foldConcatNames)(And(q, p)) === (q.id.name + p.id.name))
    assert(foldRight(foldConcatNames)(And(Seq(p, p, p, q, r))) ===
           (p.id.name + p.id.name + p.id.name + q.id.name + r.id.name))
    assert(foldRight(foldConcatNames)(Or(Seq(p, p, p, q, r))) ===
           (p.id.name + p.id.name + p.id.name + q.id.name + r.id.name))
    assert(foldRight(foldConcatNames)(Plus(x, y)) === (x.id.name + y.id.name))

    assert(foldRight(foldCountVariables)(And(p, q)) === 2)
    assert(foldRight(foldCountVariables)(And(q, p)) === 2)
    assert(foldRight(foldCountVariables)(And(p, p)) === 2)
    assert(foldRight(foldCountVariables)(And(Seq(p, p, p, q, r))) === 5)
    assert(foldRight(foldCountVariables)(Or(Seq(p, p, p, q, r))) === 5)
  }

  test("foldRight works on simple structure of nested expressions") { ctx =>
    assert(foldRight(foldConcatNames)(And(And(p, q), r)) === (p.id.name + q.id.name + r.id.name))
    assert(foldRight(foldConcatNames)(And(p, Or(q, r))) === (p.id.name + q.id.name + r.id.name))
  }

  private class LocalCounter {
    private var c = 0
    def inc() = c += 1
    def get = c
  }

  test("preTraversal works on a single node") { ctx =>
    val c = new LocalCounter
    preTraversal(e => c.inc())(x)
    assert(c.get === 1)
    preTraversal(e => c.inc())(y)
    assert(c.get === 2)

    var names: List[String] = List()
    preTraversal({
      case Variable(id) => names ::= id.name
      case _ => ()
    })(x)
    assert(names === List(x.id.name))
  }

  test("preTraversal correctly applies on every nodes on a simple expression") { ctx =>
    val c1 = new LocalCounter
    preTraversal(e => c1.inc())(And(Seq(p, q, r)))
    assert(c1.get === 4)
    val c2 = new LocalCounter
    preTraversal(e => c2.inc())(Or(p, q))
    assert(c2.get === 3)
    preTraversal(e => c2.inc())(Plus(x, y))
    assert(c2.get === 6)
  }

  test("preTraversal visits children from left to right") { ctx =>
    var names: List[String] = List()
    preTraversal({
      case Variable(id) => names ::= id.name
      case _ => ()
    })(And(List(p, q, r)))
    assert(names === List(r.id.name, q.id.name, p.id.name))
  }

  test("preTraversal works on nexted expressions") { ctx =>
    val c = new LocalCounter
    preTraversal(e => c.inc())(And(p, And(q, r)))
    assert(c.get === 5)
  }

  test("preTraversal traverses in pre-order") { ctx =>
    var nodes: List[Expr] = List()
    val node = And(List(p, q, r))
    preTraversal(e => nodes ::= e)(node)
    assert(nodes === List(r, q, p, node))
  }


  test("postTraversal works on a single node") { ctx =>
    val c = new LocalCounter
    postTraversal(e => c.inc())(x)
    assert(c.get === 1)
    postTraversal(e => c.inc())(y)
    assert(c.get === 2)

    var names: List[String] = List()
    postTraversal({
      case Variable(id) => names ::= id.name
      case _ => ()
    })(x)
    assert(names === List(x.id.name))
  }

  test("postTraversal correctly applies on every nodes on a simple expression") { ctx =>
    val c1 = new LocalCounter
    postTraversal(e => c1.inc())(And(Seq(p, q, r)))
    assert(c1.get === 4)
    val c2 = new LocalCounter
    postTraversal(e => c2.inc())(Or(p, q))
    assert(c2.get === 3)
    postTraversal(e => c2.inc())(Plus(x, y))
    assert(c2.get === 6)
  }

  test("postTraversal visits children from left to right") { ctx =>
    var names: List[String] = List()
    postTraversal({
      case Variable(id) => names ::= id.name
      case _ => ()
    })(And(List(p, q, r)))
    assert(names === List(r.id.name, q.id.name, p.id.name))
  }

  test("postTraversal works on nexted expressions") { ctx =>
    val c = new LocalCounter
    postTraversal(e => c.inc())(And(p, And(q, r)))
    assert(c.get === 5)
  }

  test("postTraversal traverses in pre-order") { ctx =>
    var nodes: List[Expr] = List()
    val node = And(List(p, q, r))
    postTraversal(e => nodes ::= e)(node)
    assert(nodes === List(node, r, q, p))
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



  test("simplifyArithmetic") { ctx =>
    val e1 = Plus(bi(3), bi(2))
    checkLikelyEq(ctx)(e1, simplifyArithmetic(e1))
    val e2 = Plus(x, Plus(bi(3), bi(2)))
    checkLikelyEq(ctx)(e2, simplifyArithmetic(e2))

    val e3 = Minus(bi(3), bi(2))
    checkLikelyEq(ctx)(e3, simplifyArithmetic(e3))
    val e4 = Plus(x, Minus(bi(3), bi(2)))
    checkLikelyEq(ctx)(e4, simplifyArithmetic(e4))
    val e5 = Plus(x, Minus(x, bi(2)))
    checkLikelyEq(ctx)(e5, simplifyArithmetic(e5))

    val e6 = Times(bi(9), Plus(Division(x, bi(3)), Division(x, bi(6))))
    checkLikelyEq(ctx)(e6, simplifyArithmetic(e6))
  }

  test("expandAndSimplifyArithmetic") { ctx =>
    val e1 = Plus(bi(3), bi(2))
    checkLikelyEq(ctx)(e1, expandAndSimplifyArithmetic(e1))
    val e2 = Plus(x, Plus(bi(3), bi(2)))
    checkLikelyEq(ctx)(e2, expandAndSimplifyArithmetic(e2))

    val e3 = Minus(bi(3), bi(2))
    checkLikelyEq(ctx)(e3, expandAndSimplifyArithmetic(e3))
    val e4 = Plus(x, Minus(bi(3), bi(2)))
    checkLikelyEq(ctx)(e4, expandAndSimplifyArithmetic(e4))
    val e5 = Plus(x, Minus(x, bi(2)))
    checkLikelyEq(ctx)(e5, expandAndSimplifyArithmetic(e5))

    val e6 = Times(bi(9), Plus(Division(x, bi(3)), Division(x, bi(6))))
    checkLikelyEq(ctx)(e6, expandAndSimplifyArithmetic(e6))
  }

  test("extractEquals") { ctx =>
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

  test("pre and post traversal") { ctx =>
    val expr = Plus(bi(1), Minus(bi(2), bi(3)))
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

  test("pre- and postMap") { ctx =>
    val expr = Plus(bi(1), Minus(bi(2), bi(3)))
    def op(e : Expr ) = e match {
      case Minus(InfiniteIntegerLiteral(two), e2) if two == BigInt(2) => Some(bi(2))
      case InfiniteIntegerLiteral(one) if one == BigInt(1) => Some(bi(2))
      case InfiniteIntegerLiteral(two) if two == BigInt(2) => Some(bi(42))
      case _ => None
    }
    
    assert( preMap(op, false)(expr) == Plus(bi(2),  bi(2))  )
    assert( preMap(op, true )(expr) == Plus(bi(42), bi(42)) )
    assert( postMap(op, false)(expr) == Plus(bi(2),  Minus(bi(42), bi(3))) )
    assert( postMap(op, true)(expr)  == Plus(bi(42), Minus(bi(42), bi(3))) )
    
  }
}
