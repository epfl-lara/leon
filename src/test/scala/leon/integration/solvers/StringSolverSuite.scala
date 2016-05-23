/* Copyright 2009-2016 EPFL, Lausanne */

package leon.integration.solvers

import org.scalatest.FunSuite
import org.scalatest.Matchers
import leon.test.helpers.ExpressionsDSL
import leon.solvers.string.StringSolver
import leon.purescala.Common.FreshIdentifier
import leon.purescala.Common.Identifier
import scala.collection.mutable.{HashMap => MMap}
import scala.concurrent.Future
import scala.concurrent.ExecutionContext.Implicits.global
import org.scalatest.concurrent.Timeouts
import org.scalatest.concurrent.ScalaFutures
import org.scalatest.time.SpanSugar._
import org.scalatest.FunSuite
import org.scalatest.concurrent.Timeouts
import org.scalatest.concurrent.ScalaFutures
import org.scalatest.time.SpanSugar._

/**
 * @author Mikael
 */
class StringSolverSuite extends FunSuite with Matchers with ScalaFutures {
  val k = new MMap[String, Identifier]
  
  val x = FreshIdentifier("x")
  val y = FreshIdentifier("y")
  val z = FreshIdentifier("z")
  val u = FreshIdentifier("u")
  val v = FreshIdentifier("v")
  val w = FreshIdentifier("w")
  k ++= List("x" -> x, "y" -> y, "z" -> z, "u" -> u, "v" -> v, "w" -> w)
  
  implicit class EquationMaker(lhs: String) {
    def convertStringToStringFrom(s: String)(implicit idMap: MMap[String, Identifier]): StringSolver.StringForm = {
      for(elem <- s.split("\\+").toList) yield {
        if(elem.startsWith("\"")) {
          Left(elem.substring(1, elem.length - 1))
        } else if(elem(0).isDigit) {
          Left(elem)
        } else {
          val id = idMap.getOrElse(elem, {
            val res = FreshIdentifier(elem)
            idMap += elem -> res
            res
          })
          Right(id)
        }
      }
    }
    
    def ===(rhs: String)(implicit k: MMap[String, Identifier]): StringSolver.Equation = {
      (convertStringToStringFrom(lhs), rhs)
    }
    def ====(rhs: String)(implicit k: MMap[String, Identifier]): StringSolver.GeneralEquation = {
      (convertStringToStringFrom(lhs), convertStringToStringFrom(rhs))
    }
  }
  
  import StringSolver._
  
  def m = MMap[String, Identifier]()
  
  test("simplifyProblem"){
    implicit val kk = k
    simplifyProblem(List("x" === "1"), Map()) should equal (Some((Nil, Map(x -> "1"))))
    simplifyProblem(List("y" === "23"), Map()) should equal (Some((Nil, Map(y -> "23"))))
    simplifyProblem(List("1" === "1"), Map()) should equal (Some((Nil, Map())))
    simplifyProblem(List("2" === "1"), Map()) should equal (None)
    simplifyProblem(List("x" === "1", "y+x" === "12"), Map()) should equal (Some((List("y+1" === "12"), Map(x -> "1"))))
  }
  
  test("noLeftRightConstants") {
    implicit val kk = k
    noLeftRightConstants(List("x" === "1"), Map()) should equal (Some((List("x" === "1"), Map())))
    noLeftRightConstants(List("y+2" === "12"), Map()) should equal (Some((List("y" === "1"), Map())))
    noLeftRightConstants(List("3+z" === "31"), Map()) should equal (Some((List("z" === "1"), Map())))
    noLeftRightConstants(List("1+u+2" === "1, 2"), Map()) should equal (Some((List("u" === ", "), Map())))
  }
  test("forwardStrategy") {
    implicit val kk = k
    forwardStrategy(List("x+3" === "123", "x+y" === "1245"), Map()) should equal (Some((Nil, Map(x -> "12", y -> "45"))))
    forwardStrategy(List("y+z" === "4567", "x+3" === "123", "x+y" === "1245"), Map()) should equal (Some((Nil, Map(x -> "12", y -> "45", z -> "67"))))
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
    implicit val stats = Map(x -> 1, y -> 1) // Dummy stats
    simpleSplit(List(), "").toList should equal (List(Map()))
    simpleSplit(List(), "abc").toList should equal (Nil)
    simpleSplit(List(x), "abc").toList should equal (List(Map(x -> "abc")))
    simpleSplit(List(x, y), "ab").toList should equal (List(Map(x -> "", y -> "ab"), Map(x -> "ab", y -> ""), Map(x -> "a", y -> "b")))
    simpleSplit(List(x, x), "ab").toList should equal (Nil)
    simpleSplit(List(x, y, x), "aba").toList should equal (List(Map(x -> "", y -> "aba"), Map(x -> "a", y -> "b")))
  }
  
  test("simpleSplitPriority") { // Just guesses some values for y.
    implicit val stats = Map(x -> 1, y -> 2)
    simpleSplit(List(x, y, y, y), "a121212").toList should equal (List(Map(y -> "12"), Map(y -> "2"), Map(y -> "")))
  }

  
  test("solve switch") {
    implicit val kk = k
    solve(List("x+y" === "1234", "y+x" === "1234")).toSet should equal (Set(Map(x -> "1234", y -> ""), Map(x -> "", y -> "1234")))
    solve(List("x+y" === "1234", "y+x" === "3412")).toList should equal (List(Map(x -> "12", y -> "34")))
    solve(List("x+y" === "1234", "y+x" === "4123")).toList should equal (List(Map(x -> "123", y -> "4")))
    solve(List("x+y" === "1234", "y+x" === "2341")).toList should equal (List(Map(x -> "1", y -> "234")))
  }

  test("solve inner") {
    implicit val kk = k
    solve(List("x+2+y" === "123")).toList should equal (List(Map(x -> "1", y -> "3")))
    solve(List("x+2+y+z" === "123")).toSet should equal (Set(Map(x -> "1", y -> "3", z -> ""), Map(x -> "1", y -> "", z -> "3")))
    solve(List("x+2+y" === "12324")).toSet should equal (Set(Map(x -> "1", y -> "324"), Map(x -> "123", y -> "4")))
  }
  
  test("isTransitivelyBounded") {
    implicit val kk = k
    isTransitivelyBounded(List("1" ==== "2")) should be(true)
    isTransitivelyBounded(List("2" ==== "2")) should be(true)
    isTransitivelyBounded(List("x+2" ==== "2")) should be(true)
    isTransitivelyBounded(List("x+2" ==== "1")) should be(true)
    isTransitivelyBounded(List("x+2" ==== "2+x")) should be(false)
    isTransitivelyBounded(List("x+2" ==== "2+y")) should be(false)
    isTransitivelyBounded(List("x+2" ==== "2+y", "y" ==== "1")) should be(true)
    isTransitivelyBounded(List("x+2" ==== "2+x", "x" ==== "1")) should be(true)
    isTransitivelyBounded(List("x+y+z" ==== "1234", "u+v" ==== "y+42+x")) should be(true)
  }
  
  test("solveGeneralProblem") {
    implicit val kk = k
    solveGeneralProblem(List("x+y" ==== "12", "u+v" ==== "y+x")).toSet should equal (
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
  
  test("constantPropagate") {
    implicit val kk = k
    val complexString = "abcdefmlkjsdqfmlkjqezpijbmkqjsdfmijzmajmpqjmfldkqsjmkj"
    solve(List("w+5+x+y+z+u+v" === (complexString+"5"))).toList should equal (
        List(Map(w -> complexString,
                 x -> "",
                 y -> "",
                 z -> "",
                 u -> "",
                 v -> "")))
  }
  
  test("constantPropagate2") {
    implicit val kk = k
    val complexString = "abcdefmlkjsdqfmlkjqezpijbmkqjsdfmijzmajmpqjmfldkqsjmkj"
    val complexString2 = complexString.reverse
    val complexString3 = "flmqmslkjdqfmleomijgmlkqsjdmfijmqzoijdfmlqksjdofijmez"
    solve(List("w+5+x+5+z" === (complexString+"5" + complexString2 + "5" + complexString3))).toList should equal (
        List(Map(w -> complexString,
                 x -> complexString2,
                 z -> complexString3)))
  }
  
  test("ListInt") {
    implicit val idMap = MMap[String, Identifier]()
    val problem = List(
        """const8+const4+"12"+const5+const+"-1"+const1+const3+const2+const6+const9""" === "(12, -1)",
        """const8+const4+"1"+const5+const3+const6+const9""" === "(1)",
        """const8+const7+const9""" === "()")
    val solutions = solve(problem)
    solutions should not be 'empty
    val solution = solutions.head
    errorcheck(problem, solution) should be(None)
  }
  
  test("ListInt as List(...)") {
    implicit val idMap = MMap[String, Identifier]()
    val problem = List("const8" ===  "List(",
        "const8+const7+const9" ===  "List()",
        """const8+const4+"1"+const5+const3+const6+const9""" === "List(1)",
        """const8+const4+"12"+const5+const+"-1"+const1+const3+const2+const6+const9""" === "List(12, -1)")
    val solution = solve(problem) 
    solution should not be 'empty
    val firstSolution = solution(0)
    firstSolution(idMap("const8")) should equal("List(")
    firstSolution(idMap("const4")) should equal("")
  }
  
  test("solveJadProblem") {
    val lhs = """const38+const34+const7+"T1"+const8+const3+const9+const5+"5"+const6+const10+const35+const30+const13+"T1"+const14+const31+const30+const7+"T2"+const8+const2+const9+const4+const10+const31+const30+const25+"T1"+const26+"Push"+const27+const20+"5"+const21+const28+const22+const29+const31+const30+const13+"T2"+const14+const31+const30+const25+"T2"+const26+"Pop"+const27+const19+const28+const23+"5"+const24+const29+const31+const33+const32+const32+const32+const32+const32+const36+const39=="T1: call Push(5)"""
    implicit val idMap = MMap[String, Identifier]()
    
    val expected = """T1: call Push(5)
T1: internal
T2: call Pop()
T1: ret Push(5)
T2: internal
T2: ret Pop() -> 5"""
    
    val problem: Problem = List(lhs === expected)
    
    solve(problem) should not be 'empty
  }
  
  test("SolvePropagateEquationProblem") {
    implicit val idMap = MMap[String, Identifier]()
    val problem = List(
        "a+b+c+d" ===    "1234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890",
        "k+a+b+c+d" === "21234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567891"
    )
    val p = Future { solve(problem) }
    assert(p.isReadyWithin(2 seconds), "Could not solve propagate")
    p.futureValue should be('empty)
  }
  
  test("SolveRightCheckingProblem") {
    implicit val idMap = MMap[String, Identifier]()
    val problem = List(
        "u+v+w+a+b+c+d" ===      "123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789",
        "u+v+w+k+a+k+b+c+d" === "21234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567892"
    )
    val p = Future { solve(problem) }
    assert(p.isReadyWithin(2 seconds), "Could not solve propagate")
    p.futureValue should not be('empty)
  }
  
  test("solveMinChange") {
    implicit val idMap = MMap[String, Identifier]()
    val problem = List(
        "u+v+w" === "akbc"
    )
    val u = idMap("u")
    val v = idMap("v")
    val w = idMap("w")
    val solutions = solveMinChange(problem, Map(u -> "a", v -> "b", w -> "c"))
    solutions(0) should equal (Map(u -> "ak"))
    solutions(1) should equal (Map(v -> "kb"))
    (2 to 5).toSet.map((i: Int) => solutions(i)) should equal (Set(Map(u -> "", v -> "akb")
    , Map(u -> "a", v -> "kb")
    , Map(u -> "ak", v -> "b")
    , Map(u -> "akb", v -> "")))
  }
}