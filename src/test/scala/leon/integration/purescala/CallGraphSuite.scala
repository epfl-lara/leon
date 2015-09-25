/* Copyright 2009-2015 EPFL, Lausanne */

package leon.integration.purescala

import leon.test._

import leon._
import leon.purescala.Definitions._
import leon.utils._

class CallGraphSuite extends LeonTestSuiteWithProgram with helpers.ExpressionsDSL {

  val sources = List(
    """object Matches {
      |  import leon.collection._
      |  def aMatch(a: List[Int]) = a match {
      |    case _ :: _ => 0
      |  }
      |}""".stripMargin
  )

  test("CallGraph tracks dependency to unapply pattern") { implicit fix =>
    val fd1 = funDef("Matches.aMatch")
    val fd2 = funDef("leon.collection.::.unapply")

    assert(implicitly[Program].callGraph.calls(fd1, fd2))
  }

}
