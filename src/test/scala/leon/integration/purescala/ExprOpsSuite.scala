/* Copyright 2009-2016 EPFL, Lausanne */

package leon.integration.purescala

import leon.test._

import leon.purescala.Constructors._
import leon.purescala.Expressions._
import leon.purescala.ExprOps._
import leon.purescala.Definitions._
import leon.purescala.Common._

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
        |}""".stripMargin,

      """object Nested {
        |  def foo = {
        |    def bar = {
        |      def baz = 42
        |      baz
        |    }
        |    def zoo = 42
        |  }
        |}
        |
      """.stripMargin
  )

  test("mapForPattern introduces casts"){ implicit fix =>
    funDef("Casts1.aMatch").body match {
      case Some(MatchExpr(scrut, Seq(MatchCase(p, None, b)))) =>
        val bar3 = caseClassDef("Casts1.Bar3").typed
        val bar4 = caseClassDef("Casts1.Bar4").typed
        val i    = caseClassDef("Casts1.Bar4").fields.head.id

        for ((id, v) <- mapForPattern(scrut, p)) {
          if (id.name == "b1") {
            assert(v === AsInstanceOf(scrut, bar4))
          } else if (id.name == "b2") {
            assert(v === AsInstanceOf(CaseClassSelector(bar4, AsInstanceOf(scrut, bar4), i), bar3))
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

  test("closing functions") { implicit fix =>
    val nested = moduleDef("Nested")
    assert(nested.definedFunctions.size === 4)
  }

  test("simplestValue") { implicit fix =>
    import leon.purescala.TypeOps.isSubtypeOf
    val act = classDef("Casts1.Foo").typed
    val cct = caseClassDef("Casts1.Bar1").typed

    assert(isSubtypeOf(simplestValue(act).getType, act))
    assert(simplestValue(cct).getType == cct)
  }
  
  test("canBeHomomorphic") { implicit fix =>
    import leon.purescala.ExprOps.canBeHomomorphic
    import leon.purescala.Types._
    import leon.purescala.Definitions._
    val d = FreshIdentifier("d", IntegerType)
    val x = FreshIdentifier("x", IntegerType)
    val y = FreshIdentifier("y", IntegerType)
    assert(canBeHomomorphic(Variable(d), Variable(x)).isEmpty)
    val l1 = Lambda(Seq(ValDef(x)), Variable(x))
    val l2 = Lambda(Seq(ValDef(y)), Variable(y))
    assert(canBeHomomorphic(l1, l2).nonEmpty)
    val fType = FunctionType(Seq(IntegerType), IntegerType)
    val f = FreshIdentifier("f",
        FunctionType(Seq(IntegerType, fType, fType), IntegerType))
    val farg1 = FreshIdentifier("arg1", IntegerType)
    val farg2 = FreshIdentifier("arg2", fType)
    val farg3 = FreshIdentifier("arg3", fType)
    
    val fdef = new FunDef(f, Seq(), Seq(ValDef(farg1), ValDef(farg2), ValDef(farg3)), IntegerType)
    
    // Captured variables should be silent, even if they share the same identifier in two places of the code.
    assert(canBeHomomorphic(
        FunctionInvocation(fdef.typed, Seq(Variable(d), l1, l2)),
        FunctionInvocation(fdef.typed, Seq(Variable(d), l1, l1))).nonEmpty)
    
    assert(canBeHomomorphic(
        StringLiteral("1"),
        StringLiteral("2")).isEmpty)
  }

}
