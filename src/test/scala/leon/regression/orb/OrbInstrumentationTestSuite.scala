/* Copyright 2009-2016 EPFL, Lausanne */

package leon.regression.orb
import leon.test._
import leon._
import leon.purescala.Definitions._
import leon.invariant.engine._
import leon.transformations._
import java.io.File
import leon.purescala.Types.TupleType

class OrbInstrumentationTestSuite extends LeonRegressionSuite {

  test("TestInstrumentation") {
    val ctx = createLeonContext("--timeout=10")
    val content =
      """
	import leon.annotation._
	import leon.invariant._
	import leon.instrumentation._

	object Test {
	  sealed abstract class List
	  case class Cons(tail: List) extends List
	  case class Nil() extends List

	  // proved with unrolling=0
	  def size(l: List) : BigInt = (l match {
	      case Nil() => BigInt(0)
	      case Cons(t) => 1 + size(t)
	  }) ensuring(res => tmpl(a => steps <= a))
	}"""
    val pipe = leon.utils.TemporaryInputPhase andThen
      leon.frontends.scalac.ExtractionPhase andThen
      new leon.utils.PreprocessingPhase andThen
      InstrumentationPhase
    val (ctx2, instProg) = pipe.run(ctx, (List(content), Nil))
    val sizeFun = instProg.definedFunctions.find(_.id.name.startsWith("size"))
    if (!sizeFun.isDefined || !sizeFun.get.returnType.isInstanceOf[TupleType])
      fail("Error in instrumentation")
  }
}
