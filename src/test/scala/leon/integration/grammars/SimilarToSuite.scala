/* Copyright 2009-2016 EPFL, Lausanne */

package leon.integration.grammars

import leon._
import leon.test._
import leon.test.helpers._
import leon.purescala.Path
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Constructors._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.codegen._
import synthesis._
import bonsai.enumerators._
import grammars._
import grammars.aspects.SimilarTo

class SimilarToSuite extends LeonTestSuiteWithProgram with ExpressionsDSL {

  val sources = List(
    """|import leon.lang._
       |import leon.annotation._
       |import leon.collection._
       |import leon._
       |
       |object Trees {
       |  abstract class Expr
       |  case class Plus(lhs: Expr, rhs: Expr) extends Expr
       |  case class Minus(lhs: Expr, rhs: Expr) extends Expr
       |  case class LessThan(lhs: Expr, rhs: Expr) extends Expr
       |  case class And(lhs: Expr, rhs: Expr) extends Expr
       |  case class Or(lhs: Expr, rhs: Expr) extends Expr
       |  case class Not(e : Expr) extends Expr
       |  case class Eq(lhs: Expr, rhs: Expr) extends Expr
       |  case class Ite(cond: Expr, thn: Expr, els: Expr) extends Expr
       |  case class IntLiteral(v: BigInt) extends Expr
       |  case class BoolLiteral(b : Boolean) extends Expr
       |}
       |object STrees {
       |  abstract class Expr
       |  case class Plus(lhs : Expr, rhs : Expr) extends Expr
       |  case class Neg(arg : Expr) extends Expr
       |  case class Ite(cond : Expr, thn : Expr, els : Expr) extends Expr
       |  case class Eq(lhs : Expr, rhs : Expr) extends Expr
       |  case class LessThan(lhs : Expr, rhs : Expr) extends Expr
       |  case class Literal(i : BigInt) extends Expr
       |}
       |
       |object Desugar {
       |  def desugar(e: Trees.Expr): STrees.Expr = {
       |    STrees.Literal(0)
       |  }
       |} """.stripMargin,

    """|import leon.lang._
       |import leon.collection._
       |
       |object Heaps {
       |
       |  sealed abstract class Heap {
       |    val rank : BigInt = this match {
       |      case Leaf() => 0
       |      case Node(_, l, r) => 
       |        1 + max(l.rank, r.rank)
       |    }
       |    def content : Set[BigInt] = this match {
       |      case Leaf() => Set[BigInt]()
       |      case Node(v,l,r) => l.content ++ Set(v) ++ r.content
       |    }
       |  }
       |  case class Leaf() extends Heap
       |  case class Node(value:BigInt, left: Heap, right: Heap) extends Heap
       |
       |  def max(i1 : BigInt, i2 : BigInt) = if (i1 >= i2) i1 else i2
       |
       |  def hasHeapProperty(h : Heap) : Boolean = h match {
       |    case Leaf() => true
       |    case Node(v, l, r) => 
       |      ( l match {
       |        case Leaf() => true
       |        case n@Node(v2,_,_) => v >= v2 && hasHeapProperty(n)
       |      }) && 
       |      ( r match {
       |        case Leaf() => true
       |        case n@Node(v2,_,_) => v >= v2 && hasHeapProperty(n)
       |      })
       |  }
       |
       |  def hasLeftistProperty(h: Heap) : Boolean = h match {
       |    case Leaf() => true
       |    case Node(_,l,r) => 
       |      hasLeftistProperty(l) && 
       |      hasLeftistProperty(r) && 
       |      l.rank >= r.rank 
       |  }
       |
       |  def heapSize(t: Heap): BigInt = { t match {
       |    case Leaf() => BigInt(0)
       |    case Node(v, l, r) => heapSize(l) + 1 + heapSize(r)
       |  }} ensuring(_ >= 0)
       |
       |  private def merge(h1: Heap, h2: Heap) : Heap = {
       |    require(
       |      hasLeftistProperty(h1) && hasLeftistProperty(h2) && 
       |      hasHeapProperty(h1) && hasHeapProperty(h2)
       |    )
       |    (h1,h2) match {
       |      case (Leaf(), _) => h2
       |      case (_, Leaf()) => h1
       |      case (Node(v1, l1, r1), Node(v2, l2, r2)) =>
       |        //if(v1 >= v2) // FIXME
       |          makeN(v1, l1, merge(r1, h2))
       |        //else
       |        //  makeN(v2, l2, merge(h1, r2))
       |    }
       |  } ensuring { res => 
       |    hasLeftistProperty(res) && hasHeapProperty(res) &&
       |    heapSize(h1) + heapSize(h2) == heapSize(res) &&
       |    h1.content ++ h2.content == res.content 
       |  }
       |
       |  private def makeN(value: BigInt, left: Heap, right: Heap) : Heap = {
       |    require(
       |      hasLeftistProperty(left) && hasLeftistProperty(right)
       |    )
       |    if(left.rank >= right.rank)
       |      Node(value, left, right)
       |    else
       |      Node(value, right, left)
       |  } ensuring { res =>
       |    hasLeftistProperty(res)  }
       |}""".stripMargin

  )

  def runTests(tests: List[(List[Variable], Expr, Expr)], ofd: Option[FunDef] = None)(implicit fix: (LeonContext, Program)): Unit = {
    for ((vs, from, exp) <- tests) {
      // SimilarTo(<from>) should produce <exp>

      val g = OneOf(vs)
      val enum = new MemoizedEnumerator[Label, Expr, ProductionRule[Label, Expr]](g.getProductions)
      val exprs = enum.iterator(Label(exp.getType).withAspect(SimilarTo(Seq(from))))

      //println(s"SimilarTo(${from.asString}):")

      if (!exprs.contains(exp)) {
        info("Productions: ")
        g.printProductions(info(_))

        fail(s"Unable to find ${exp.asString} in SimilarTo(${from.asString})")
      }
    }
  }

  test("Basic") { implicit fix =>

    def _None = CaseClass(caseClassDef("leon.lang.None").typed(Seq(IntegerType)), Nil)
    def _Some(e: Expr) = CaseClass(caseClassDef("leon.lang.Some").typed(Seq(IntegerType)), List(e))

    val tests = List[(List[Variable], Expr, Expr)](
      (List(x, y), GreaterThan(x, y), GreaterThan(y, x)),
      (List(x, y), GreaterThan(x, y), not(GreaterThan(x, y))),
      (List(x, y), equality(x, y), not(equality(x, y))),
      (List(x, y), x, y),
      (List(x), _Some(x), _Some(Plus(x, bi(1)))),
      (List(x), _Some(Plus(x, bi(2))), _Some(Plus(x, bi(1))))
    )

    runTests(tests)
  }

  test("Desugar") { implicit fix =>
    val e    = id("e", "Trees.Expr").toVariable
    val cond = id("cond", "Trees.Expr").toVariable
    val thn  = id("thn", "Trees.Expr").toVariable
    val els  = id("els", "Trees.Expr").toVariable

    def Ite(es: Expr*) = cc("STrees.Ite")(es: _*)
    def Literal(es: Expr*) = cc("STrees.Literal")(es: _*)

    val desugarfd = funDef("Desugar.desugar")
    def desugar(es: Expr*) = fcall("Desugar.desugar")(es: _*)

    val tests = List[(List[Variable], Expr, Expr)](
      (List(cond, thn, els),
       Ite(desugar(cond), desugar(els), desugar(thn)),
       Ite(desugar(cond), desugar(thn), desugar(els))
      ),
      (List(e),
       Ite(desugar(e), Literal(bi(1)), Literal(bi(1))),
       Ite(desugar(e), Literal(bi(0)), Literal(bi(1)))
      )
    )

    runTests(tests, Some(desugarfd))
  }

  test("Heap") { implicit fix =>
    val v1   = id("v1", IntegerType).toVariable
    val h1   = id("h1", "Heaps.Heap").toVariable
    val l1   = id("l1", "Heaps.Heap").toVariable
    val r1   = id("r1", "Heaps.Heap").toVariable

    val v2   = id("v2", IntegerType).toVariable
    val h2   = id("h2", "Heaps.Heap").toVariable
    val l2   = id("l2", "Heaps.Heap").toVariable
    val r2   = id("r2", "Heaps.Heap").toVariable

    val mergefd = funDef("Heaps.merge")
    def merge(es: Expr*) = fcall("Heaps.merge")(es: _*)

    def makeN(es: Expr*) = fcall("Heaps.makeN")(es: _*)

    def Node(es: Expr*) = cc("Heaps.Node")(es: _*)
    def Leaf(es: Expr*) = cc("Heaps.Leaf")(es: _*)

    def rank(es: Expr*) = fcall("Heap.rank")(es: _*)

    val tests = List[(List[Variable], Expr, Expr)](
      (List(h1, v1, l1, r1, h2, v2, l2, r2),
       makeN(v2, l1, merge(h1, r2)),
       makeN(v2, l2, merge(h1, r2))
      ),
      (List(v1, h1),
       merge(Node(Plus(v1, bi(1)), Leaf(), Leaf()), h1),
      merge(Node(v1, Leaf(), Leaf()), h1)
      ),
      (List(h1, h2),
       GreaterThan(rank(h1), Plus(rank(h2), bi(42))),
       GreaterThan(rank(h1), Minus(Plus(rank(h2), bi(42)), bi(1)))
      )
    )

    runTests(tests, Some(mergefd))
  }
}
