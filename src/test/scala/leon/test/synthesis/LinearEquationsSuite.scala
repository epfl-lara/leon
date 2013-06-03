/* Copyright 2009-2013 EPFL, Lausanne */

package leon.test.synthesis

import org.scalatest.FunSuite

import leon.purescala.Trees._
import leon.purescala.TypeTrees._
import leon.purescala.TreeOps._
import leon.purescala.Common._
import leon.test.purescala.LikelyEq

import leon.synthesis.LinearEquations._

class LinearEquationsSuite extends FunSuite {

  def i(x: Int) = IntLiteral(x)

  val xId = FreshIdentifier("x").setType(Int32Type)
  val x = Variable(xId)
  val yId = FreshIdentifier("y").setType(Int32Type)
  val y = Variable(yId)
  val zId = FreshIdentifier("z").setType(Int32Type)
  val z = Variable(zId)

  val aId = FreshIdentifier("a").setType(Int32Type)
  val a = Variable(aId)
  val bId = FreshIdentifier("b").setType(Int32Type)
  val b = Variable(bId)

  def toSum(es: Seq[Expr]) = es.reduceLeft(Plus(_, _))
  
  def checkSameExpr(e1: Expr, e2: Expr, vs: Set[Identifier], prec: Expr, defaultMap: Map[Identifier, Expr] = Map()) {
    assert( //this outer assert should not be needed because of the nested one
      LikelyEq(e1, e2, vs, prec, (e1, e2) => {assert(e1 === e2); true}, defaultMap)
    )
  }


  //use some random values to check that any vector in the basis is a valid solution to
  //the equation
  def checkVectorSpace(basis: Array[Array[Int]], equation: Array[Int]) {
    require(basis.size == basis(0).size + 1 && basis.size == equation.size)
    val n = basis(0).size
    val min = -5
    val max = 5
    val components = Array.fill(n)(min)
    var counter = 0

    while(counter < n) {
      val sol = mult(basis, components) //one linear combination of the basis
      assert(eval(sol, equation) === 0)

      //next components
      if(components(counter) < max)
        components(counter) += 1
      else {
        while(counter < n && components(counter) >= max) {
          components(counter) = min
          counter += 1
        }
        if(counter < n) {
          components(counter) += 1
          counter = 0
        }
      }
    }
  }

  //val that the sol vector with the term in the equation
  def eval(sol: Array[Int], equation: Array[Int]): Int = {
    require(sol.size == equation.size)
    sol.zip(equation).foldLeft(0)((acc, p) => acc + p._1 * p._2)
  }

  //multiply the matrix by the vector: [M1 M2 .. Mn] * [v1 .. vn] = v1*M1 + ... + vn*Mn]
  def mult(matrix: Array[Array[Int]], vector: Array[Int]): Array[Int] = {
    require(vector.size == matrix(0).size && vector.size > 0)
    val tmat = matrix.transpose
    var tmp: Array[Int] = null
    tmp = mult(vector(0), tmat(0))
    var i = 1
    while(i < vector.size) {
      tmp = add(tmp, mult(vector(i), tmat(i)))
      i += 1
    }
    tmp
  }

  def mult(c: Int, v: Array[Int]): Array[Int] = v.map(_ * c)
  def add(v1: Array[Int], v2: Array[Int]): Array[Int] = {
    require(v1.size == v2.size)
    v1.zip(v2).map(p => p._1 + p._2)
  }

  test("checkVectorSpace") {
    checkVectorSpace(Array(Array(1), Array(2)), Array(-2, 1))
    checkVectorSpace(Array(Array(4, 0), Array(-3, 2), Array(0, -1)), Array(3, 4, 8))
  }

  
  test("particularSolution basecase") {
    def toExpr(es: Array[Expr]): Expr = {
      val coef: Array[Expr] = es
      val vars: Array[Expr] = Array[Expr](IntLiteral(1)) ++ Array[Expr](x, y)
      es.zip(vars).foldLeft[Expr](IntLiteral(0))( (acc: Expr, p: (Expr, Expr)) => Plus(acc, Times(p._1, p._2)) )
    }

    val t1: Expr = Plus(a, b)
    val c1: Expr = IntLiteral(4)
    val d1: Expr = IntLiteral(22)
    val e1: Array[Expr] = Array(t1, c1, d1)
    val (pre1, (w1, w2)) = particularSolution(Set(aId, bId), t1, c1, d1)
    checkSameExpr(toExpr(e1), IntLiteral(0), Set(aId, bId), pre1, Map(xId -> w1, yId -> w2))

    val t2: Expr = IntLiteral(-1)
    val c2: Expr = IntLiteral(1)
    val d2: Expr = IntLiteral(-1)
    val e2: Array[Expr] = Array(t2, c2, d2)
    val (pre2, (w3, w4)) = particularSolution(Set(), t2, c2, d2)
    checkSameExpr(toExpr(e2), IntLiteral(0), Set(), pre2, Map(xId -> w3, yId -> w4))
  }

  test("particularSolution preprocess") {
    def toExpr(es: Array[Expr], vs: Array[Expr]): Expr = {
      val coef: Array[Expr] = es
      val vars: Array[Expr] = Array[Expr](IntLiteral(1)) ++ vs
      es.zip(vars).foldLeft[Expr](IntLiteral(0))( (acc: Expr, p: (Expr, Expr)) => Plus(acc, Times(p._1, p._2)) )
    }

    val t1: Expr = Plus(a, b)
    val c1: Expr = IntLiteral(4)
    val d1: Expr = IntLiteral(22)
    val e1: Array[Expr] = Array(t1, c1, d1)
    val (pre1, s1) = particularSolution(Set(aId, bId), e1.toList)
    checkSameExpr(toExpr(e1, Array(x, y)), IntLiteral(0), Set(aId, bId), pre1, Array(xId, yId).zip(s1).toMap)

    val t2: Expr = Plus(a, b)
    val c2: Expr = IntLiteral(4)
    val d2: Expr = IntLiteral(22)
    val f2: Expr = IntLiteral(10)
    val e2: Array[Expr] = Array(t2, c2, d2, f2)
    val (pre2, s2) = particularSolution(Set(aId, bId), e2.toList)
    checkSameExpr(toExpr(e2, Array(x, y, z)), IntLiteral(0), Set(aId, bId), pre2, Array(xId, yId, zId).zip(s2).toMap)

    val t3: Expr = Plus(a, Times(IntLiteral(2), b))
    val c3: Expr = IntLiteral(6)
    val d3: Expr = IntLiteral(24)
    val f3: Expr = IntLiteral(9)
    val e3: Array[Expr] = Array(t3, c3, d3, f3)
    val (pre3, s3) = particularSolution(Set(aId, bId), e3.toList)
    checkSameExpr(toExpr(e3, Array(x, y, z)), IntLiteral(0), Set(aId, bId), pre3, Array(xId, yId, zId).zip(s3).toMap)

    val t4: Expr = Plus(a, b)
    val c4: Expr = IntLiteral(4)
    val e4: Array[Expr] = Array(t4, c4)
    val (pre4, s4) = particularSolution(Set(aId, bId), e4.toList)
    checkSameExpr(toExpr(e4, Array(x)), IntLiteral(0), Set(aId, bId), pre4, Array(xId).zip(s4).toMap)
  }


  test("linearSet") {
    val as = Set[Identifier]()

    val eq1 = Array(3, 4, 8)
    val basis1 = linearSet(as, eq1)
    checkVectorSpace(basis1, eq1)

    val eq2 = Array(1, 2, 3)
    val basis2 = linearSet(as, eq2)
    checkVectorSpace(basis2, eq2)

    val eq3 = Array(1, 1)
    val basis3 = linearSet(as, eq3)
    checkVectorSpace(basis3, eq3)

    val eq4 = Array(1, 1, 2, 7)
    val basis4 = linearSet(as, eq4)
    checkVectorSpace(basis4, eq4)

    val eq5 = Array(1, -1)
    val basis5 = linearSet(as, eq5)
    checkVectorSpace(basis5, eq5)

    val eq6 = Array(1, -6, 3)
    val basis6 = linearSet(as, eq6)
    checkVectorSpace(basis6, eq6)
  }


  def enumerate(nbValues: Int, app: (Array[Int] => Unit)) {
    val min = -5
    val max = 5
    val counters: Array[Int] = (1 to nbValues).map(_ => min).toArray
    var i = 0

    while(i < counters.size) {
      app(counters)
      if(counters(i) < max)
        counters(i) += 1
      else {
        while(i < counters.size && counters(i) >= max) {
          counters(i) = min
          i += 1
        }
        if(i < counters.size) {
          counters(i) += 1
          i = 0
        }
      }
    }

  }

  //TODO: automatic check result
  test("elimVariable") {
    val as = Set[Identifier](aId, bId)

    def check(t: Expr, c: List[Expr], prec: Expr, witnesses: List[Expr], freshVars: List[Identifier]) {
      enumerate(freshVars.size, (vals: Array[Int]) => {
        val mapping: Map[Expr, Expr] = (freshVars.zip(vals.toList).map(t => (Variable(t._1), IntLiteral(t._2))).toMap)
        val cWithVars: Expr = c.zip(witnesses).foldLeft[Expr](IntLiteral(0)){ case (acc, (coef, wit)) => Plus(acc, Times(coef, replace(mapping, wit))) }
        checkSameExpr(Plus(t, cWithVars), IntLiteral(0), as, prec)
      })
    }

    val t1 = Minus(Times(IntLiteral(2), a), b)
    val c1 = List(IntLiteral(3), IntLiteral(4), IntLiteral(8))
    val (pre1, wit1, f1) = elimVariable(as, t1::c1)
    check(t1, c1, pre1, wit1, f1)

    val t2 = Plus(Plus(IntLiteral(0), IntLiteral(2)), Times(IntLiteral(-1), IntLiteral(3)))
    val c2 = List(IntLiteral(1), IntLiteral(-1))
    val (pre2, wit2, f2) = elimVariable(Set(), t2::c2)
    check(t2, c2, pre2, wit2, f2)


    val t3 = Minus(Times(IntLiteral(2), a), IntLiteral(3))
    val c3 = List(IntLiteral(2))
    val (pre3, wit3, f3) = elimVariable(Set(aId), t3::c3)
    check(t3, c3, pre3, wit3, f3)

    val t4 = Times(IntLiteral(2), a)
    val c4 = List(IntLiteral(2), IntLiteral(4))
    val (pre4, wit4, f4) = elimVariable(Set(aId), t4::c4)
    check(t4, c4, pre4, wit4, f4)

    val t5 = Minus(a, b)
    val c5 = List(IntLiteral(-60), IntLiteral(-3600))
    val (pre5, wit5, f5) = elimVariable(Set(aId, bId), t5::c5)
    check(t5, c5, pre5, wit5, f5)

  }

}
