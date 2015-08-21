/* Copyright 2009-2015 EPFL, Lausanne */

package leon.integration.purescala

import leon.test._

import leon._
import leon.purescala.Constructors._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.ExprOps._
import leon.purescala.DefOps._
import leon.purescala.Common._
import leon.utils._

class ExprOpsSuite extends LeonTestSuiteWithProgram with helpers.ExpressionsDSL {

  val sources = List(
      """object Casts1 {
        |  abstract class Foo
        |  case class Bar1(v: BigInt) extends Foo
        |  case class Bar2(v: BigInt) extends Foo
        |  case class Bar3(v: BigInt) extends Foo
        |  case class Bar4(i: Foo) extends Foo
        |
        |  def aMatch(a: Foo) = a match {
        |    case b1 @ Bar4(b2: Bar3) => b2
        |  }
        |}""".stripMargin
  )

  test("mapForPattern introduces casts"){ implicit fix =>
    funDef("Casts1.aMatch").body match {
      case Some(MatchExpr(scrut, Seq(MatchCase(p, None, b)))) =>
        val m = mapForPattern(scrut, p)
        val bar4 = caseClassDef("Casts1.Bar4").typed
        val i    = caseClassDef("Casts1.Bar4").fields.head.id

        for ((id, v) <- mapForPattern(scrut, p)) {
          if (id.name == "b1") {
            assert(v === AsInstanceOf(scrut, bar4))
          } else if (id.name == "b2") {
            assert(v === CaseClassSelector(bar4, AsInstanceOf(scrut, bar4), i))
          } else {
            fail("Map contained unknown entry "+id.asString)
          }
        }

      case b =>
        fail("unexpected test shape: "+b)
    }
  }

  test("matchToIfThenElse introduces casts"){ implicit fix =>
    funDef("Casts1.aMatch").body match {
      case Some(b) =>
        assert(exists {
          case AsInstanceOf(_, _) => true
          case _ => false
        }(matchToIfThenElse(b)), "Could not find AsInstanceOf in the result of matchToIfThenElse")

      case b =>
        fail("unexpected test shape: "+b)
    }
  }

  test("asInstOf simplifies trivial casts") { implicit fix =>
    val cct = caseClassDef("Casts1.Bar1").typed
    val cc = CaseClass(cct, Seq(bi(42)))
    assert(asInstOf(cc, cct) === cc)
  }

  test("asInstOf leaves unknown casts") { implicit fix =>
    val act = classDef("Casts1.Foo").typed
    val cct = caseClassDef("Casts1.Bar1").typed

    val cc = CaseClass(cct, Seq(bi(42)))
    val id = FreshIdentifier("tmp", act)
    val expr = Let(id, cc, id.toVariable)

    assert(asInstOf(expr, cct) === AsInstanceOf(expr, cct))
  }
}
