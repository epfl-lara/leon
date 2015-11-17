package leon.integration.solvers

import org.scalatest.FunSuite
import org.scalatest.Matchers
import leon.test.helpers.ExpressionsDSL
import leon.solvers.string.StringSolver
import leon.purescala.Common.FreshIdentifier

/**
 * @author Mikael
 */
class StringSolverSuite extends FunSuite with Matchers {
  val k = "xyzuvw".toSeq.map((k: Char) => k -> FreshIdentifier(k.toString)).toMap
  lazy val x = k('x')
  lazy val y = k('y')
  lazy val z = k('z')
  lazy val u = k('u')
  lazy val v = k('v')
  
  implicit class EquationMaker(lhs: String) {
    def convertStringToStringFrom(s: String) = {
      s.toList.map((c: Char) => (k.get(c) match {case Some(v) => Right(v) case _ => Left(c.toString) }): StringSolver.StringFormToken)
    }
    
    def ===(rhs: String): StringSolver.Equation = {
      (convertStringToStringFrom(lhs), rhs)
    }
    def ====(rhs: String): StringSolver.GeneralEquation = {
      (convertStringToStringFrom(lhs), convertStringToStringFrom(rhs))
    }
  }
  
  import StringSolver._
  
  test("simplifyProblem"){
    simplifyProblem(List("x" === "1"), Map()) should equal (Some((Nil, Map(x -> "1"))))
    simplifyProblem(List("y" === "23"), Map()) should equal (Some((Nil, Map(y -> "23"))))
    simplifyProblem(List("1" === "1"), Map()) should equal (Some((Nil, Map())))
    simplifyProblem(List("2" === "1"), Map()) should equal (None)
    simplifyProblem(List("x" === "1", "yx" === "12"), Map()) should equal (Some((List("y1" === "12"), Map(x -> "1"))))
  }
  
  test("noLeftRightConstants") {
    noLeftRightConstants(List("x" === "1")) should equal (Some(List("x" === "1")))
    noLeftRightConstants(List("y2" === "12")) should equal (Some(List("y" === "1")))
    noLeftRightConstants(List("3z" === "31")) should equal (Some(List("z" === "1")))
    noLeftRightConstants(List("1u2" === "1, 2")) should equal (Some(List("u" === ", ")))
  }
  test("forwardStrategy") {
    forwardStrategy(List("x3" === "123", "xy" === "1245"), Map()) should equal (Some((Nil, Map(x -> "12", y -> "45"))))
    forwardStrategy(List("yz" === "4567", "x3" === "123", "xy" === "1245"), Map()) should equal (Some((Nil, Map(x -> "12", y -> "45", z -> "67"))))
  }
  
  test("occurrences") {
    occurrences("*?)*","*?)*?)**?)*???*") should equal (List(0, 3, 7))
  }
  
  test("repartitions") {
    repartitions(List("*"), "?*???????") should equal (List(List(1)))
    repartitions(List("*","*"), "?*???????") should equal (List())
    repartitions(List("1","2"), "?*1??2???") should equal (List(List(2, 5)))
    repartitions(List("*","*"), "?*????*???*") should equal (List(List(1, 6), List(1, 10), List(6, 10)))
  }
  
  test("simpleSplit") {
    simpleSplit(List(), "").toList should equal (List(Map()))
    simpleSplit(List(), "abc").toList should equal (Nil)
    simpleSplit(List(x), "abc").toList should equal (List(Map(x -> "abc")))
    simpleSplit(List(x, y), "ab").toList should equal (List(Map(x -> "", y -> "ab"), Map(x -> "a", y -> "b"), Map(x -> "ab", y -> "")))
    simpleSplit(List(x, x), "ab").toList should equal (Nil)
    simpleSplit(List(x, y, x), "aba").toList should equal (List(Map(x -> "", y -> "aba"), Map(x -> "a", y -> "b")))
  }

  
  test("solve switch") {
    solve(List("xy" === "1234", "yx" === "1234")).toSet should equal (Set(Map(x -> "1234", y -> ""), Map(x -> "", y -> "1234")))
    solve(List("xy" === "1234", "yx" === "3412")).toList should equal (List(Map(x -> "12", y -> "34")))
    solve(List("xy" === "1234", "yx" === "4123")).toList should equal (List(Map(x -> "123", y -> "4")))
    solve(List("xy" === "1234", "yx" === "2341")).toList should equal (List(Map(x -> "1", y -> "234")))
  }

  test("solve inner") {
    solve(List("x2y" === "123")).toList should equal (List(Map(x -> "1", y -> "3")))
    solve(List("x2yz" === "123")).toSet should equal (Set(Map(x -> "1", y -> "3", z -> ""), Map(x -> "1", y -> "", z -> "3")))
    solve(List("x2y" === "12324")).toSet should equal (Set(Map(x -> "1", y -> "324"), Map(x -> "123", y -> "4")))
  }
  
  test("isTransitivelyBounded") {
    isTransitivelyBounded(List("1" ==== "2")) should be(true)
    isTransitivelyBounded(List("2" ==== "2")) should be(true)
    isTransitivelyBounded(List("x2" ==== "2")) should be(true)
    isTransitivelyBounded(List("x2" ==== "1")) should be(true)
    isTransitivelyBounded(List("x2" ==== "2x")) should be(false)
    isTransitivelyBounded(List("x2" ==== "2y")) should be(false)
    isTransitivelyBounded(List("x2" ==== "2y", "y" ==== "1")) should be(true)
    isTransitivelyBounded(List("x2" ==== "2x", "x" ==== "1")) should be(true)
    isTransitivelyBounded(List("xyz" ==== "1234", "uv" ==== "y42x")) should be(true)
  }
  
  test("solveGeneralProblem") {
    solveGeneralProblem(List("xy" ==== "12", "uv" ==== "yx")).toSet should equal (
        Set(
            Map(x -> "", y -> "12", u -> "", v -> "12"),
            Map(x -> "", y -> "12", u -> "1", v -> "2"),
            Map(x -> "", y -> "12", u -> "12", v -> ""),
            Map(x -> "1", y -> "2", u -> "", v -> "21"),
            Map(x -> "1", y -> "2", u -> "2", v -> "1"),
            Map(x -> "1", y -> "2", u -> "21", v -> ""),
            Map(x -> "12", y -> "", u -> "", v -> "12"),
            Map(x -> "12", y -> "", u -> "1", v -> "2"),
            Map(x -> "12", y -> "", u -> "12", v -> "")
        )
    )
  }
}