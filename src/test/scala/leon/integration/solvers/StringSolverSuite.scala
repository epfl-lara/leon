package leon.integration.solvers

import org.scalatest.FunSuite
import org.scalatest.Matchers
import leon.test.helpers.ExpressionsDSL
import leon.solvers.string.StringSolver
import leon.purescala.Common.FreshIdentifier
import leon.purescala.Common.Identifier

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
  lazy val w = k('w')
  
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
    implicit val stats = Map(x -> 1, y -> 1) // Dummy stats
    simpleSplit(List(), "").toList should equal (List(Map()))
    simpleSplit(List(), "abc").toList should equal (Nil)
    simpleSplit(List(x), "abc").toList should equal (List(Map(x -> "abc")))
    simpleSplit(List(x, y), "ab").toList should equal (List(Map(x -> "", y -> "ab"), Map(x -> "ab", y -> ""), Map(x -> "a", y -> "b")))
    simpleSplit(List(x, x), "ab").toList should equal (Nil)
    simpleSplit(List(x, y, x), "aba").toList should equal (List(Map(x -> "", y -> "aba"), Map(x -> "a", y -> "b")))
  }
  
  test("simpleSplitPriority") {
    implicit val stats = Map(x -> 1, y -> 2)
    simpleSplit(List(x, y, y, y), "a121212").toList should equal (List(Map(y -> "1"), Map(y -> "12"), Map(y -> "2"), Map(y -> "")))
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
  
  test("constantPropagate") {
    val complexString = "abcdefmlkjsdqfmlkjqezpijbmkqjsdfmijzmajmpqjmfldkqsjmkj"
    solve(List("w5xyzuv" === (complexString+"5"))).toList should equal (
        List(Map(w -> complexString,
                 x -> "",
                 y -> "",
                 z -> "",
                 u -> "",
                 v -> "")))
  }
  
  test("constantPropagate2") {
    val complexString = "abcdefmlkjsdqfmlkjqezpijbmkqjsdfmijzmajmpqjmfldkqsjmkj"
    val complexString2 = complexString.reverse
    val complexString3 = "flmqmslkjdqfmleomijgmlkqsjdmfijmqzoijdfmlqksjdofijmez"
    solve(List("w5x5z" === (complexString+"5" + complexString2 + "5" + complexString3))).toList should equal (
        List(Map(w -> complexString,
                 x -> complexString2,
                 z -> complexString3)))
  }
  
  test("ListInt") {
    var idMap = Map[String, Identifier]()
    def makeSf(lhs: String): StringForm = {
      for(elem <- lhs.split("\\+").toList) yield {
        if(elem.startsWith("\"")) {
          Left(elem.substring(1, elem.length - 1))
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
    val lhs1 = makeSf("""const8+const4+"12"+const5+const+"-1"+const1+const3+const2+const6+const9""")
    val lhs2 = makeSf("""const8+const4+"1"+const5+const3+const6+const9""")
    val lhs3 = makeSf("""const8+const7+const9""")
    val rhs1 = "(12, -1)"
    val rhs2 = "(1)"
    val rhs3 = "()"
    val problem = List((lhs1, rhs1), (lhs2, rhs2), (lhs3, rhs3))
    solve(problem) should not be 'empty
  }
  
  test("solveJadProblem") {
    val lhs = """const26+const22+const7+const+const8+const3+const9+const5+"5"+const6+const10+const23+const18+const11+const+const12+const19+const18+const7+const1+const8+const2+const9+const4+const10+const19+const18+const13+const+const14+const3+const15+const5+"5"+const6+const16+const4+const17+const19+const18+const11+const1+const12+const19+const18+const13+const1+const14+const2+const15+const4+const16+const5+"5"+const6+const17+const19+const21+const20+const20+const20+const20+const20+const24+const27"""
    var idMap = Map[String, Identifier]()
    val lhsSf = for(elem <- lhs.split("\\+")) yield {
      if(elem.startsWith("\"")) {
        Left(elem.substring(1, elem.length - 1))
      } else {
        val id = idMap.getOrElse(elem, {
          val res = FreshIdentifier(elem)
          idMap += elem -> res
          res
        })
        Right(id)
      }
    }
    
    val expected = """T1: call Push(5)
T1: internal
T2: call Pop()
T1: ret Push(5)
T2: internal
T2: ret Pop() -> 5"""
    
    val problem: Problem = List((lhsSf.toList, expected))
    println("Problem to solve:" + StringSolver.renderProblem(problem))
    
    solve(problem) should not be 'empty
  }
}