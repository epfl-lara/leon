/* Copyright 2009-2015 EPFL, Lausanne */

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
    val ctx = createLeonContext("--inferInv", "--minbounds", "--timeout=" + 10)
    val testFilename = toTempFile(
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
	  }) ensuring(res => tmpl(a => time <= a))
	}""")
    val beginPipe = leon.frontends.scalac.ExtractionPhase andThen
      new leon.utils.PreprocessingPhase
    val program = beginPipe.run(ctx)(testFilename)
    val processPipe = InstrumentationPhase
    // check properties.
    val instProg = processPipe.run(ctx)(program)
    val sizeFun = instProg.definedFunctions.find(_.id.name.startsWith("size"))
    if(!sizeFun.isDefined || !sizeFun.get.returnType.isInstanceOf[TupleType])
      fail("Error in instrumentation")
  }

  def toTempFile(content: String): List[String] = {
    val pipeline = leon.utils.TemporaryInputPhase
    pipeline.run(createLeonContext())((List(content), Nil))
  }
}
