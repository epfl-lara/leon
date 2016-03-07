/* Copyright 2009-2016 EPFL, Lausanne */

package leon.unit.synthesis
import leon.test._

import leon.LeonContext
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.purescala.ExprOps._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.evaluators._

import leon.synthesis.LinearEquations._

class LinearEquationsSuite extends LeonTestSuite with helpers.WithLikelyEq with helpers.ExpressionsDSL {

  val aa = FreshIdentifier("aa", IntegerType).toVariable
  val bb = FreshIdentifier("bb", IntegerType).toVariable

  //use some random values to check that any vector in the basis is a valid solution to
  //the equation
  def checkVectorSpace(basis: Array[Array[Int]], equation: Array[Int]): Unit = 
    checkVectorSpace(basis.map(_.map(i => BigInt(i))), equation.map(i => BigInt(i)))

  def checkVectorSpace(basis: Array[Array[BigInt]], equation: Array[BigInt]): Unit = {
    require(basis.length == basis(0).length + 1 && basis.length == equation.length)
    val n = basis(0).length
    val min: BigInt = -5
    val max: BigInt = 5
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

  def checkSameExpr(e1: Expr, e2: Expr, pre: Expr, vs: Map[Identifier, Expr] = Map())(implicit ctx: LeonContext): Unit = {
    checkLikelyEq(ctx)(e1, e2, Some(pre), vs)
  }

  //val that the sol vector with the term in the equation
  def eval(sol: Array[BigInt], equation: Array[BigInt]): BigInt = {
    require(sol.length == equation.length)
    sol.zip(equation).foldLeft(BigInt(0))((acc, p) => acc + p._1 * p._2)
  }

  //multiply the matrix by the vector: [M1 M2 .. Mn] * [v1 .. vn] = v1*M1 + ... + vn*Mn]
  def mult(matrix: Array[Array[BigInt]], vector: Array[BigInt]): Array[BigInt] = {
    require(vector.length == matrix(0).length && vector.length > 0)
    val tmat = matrix.transpose
    var tmp: Array[BigInt] = null
    tmp = mult(vector(0), tmat(0))
    var i = 1
    while(i < vector.length) {
      tmp = add(tmp, mult(vector(i), tmat(i)))
      i += 1
    }
    tmp
  }

  def mult(c: BigInt, v: Array[BigInt]): Array[BigInt] = v.map(_ * c)
  def add(v1: Array[BigInt], v2: Array[BigInt]): Array[BigInt] = {
    require(v1.length == v2.length)
    v1.zip(v2).map(p => p._1 + p._2)
  }

  test("checkVectorSpace") { implicit ctx =>
    checkVectorSpace(Array(Array(1), Array(2)), Array(-2, 1))
    checkVectorSpace(Array(Array(4, 0), Array(-3, 2), Array(0, -1)), Array(3, 4, 8))
  }

  
  test("particularSolution basecase") { implicit ctx =>
    def toExpr(es: Array[Expr]): Expr = {
      val vars: Array[Expr] = Array[Expr](bi(1)) ++ Array[Expr](x, y)
      es.zip(vars).foldLeft[Expr](bi(0))( (acc: Expr, p: (Expr, Expr)) => Plus(acc, Times(p._1, p._2)) )
    }

    val t1: Expr = Plus(aa, bb)
    val c1: Expr = bi(4)
    val d1: Expr = bi(22)
    val e1: Array[Expr] = Array(t1, c1, d1)
    val (pre1, (w1, w2)) = particularSolution(Set(aa.id, bb.id), t1, c1, d1)
    checkSameExpr(toExpr(e1), bi(0), pre1, Map(x.id -> w1, y.id -> w2))

    val t2: Expr = bi(-1)
    val c2: Expr = bi(1)
    val d2: Expr = bi(-1)
    val e2: Array[Expr] = Array(t2, c2, d2)
    val (pre2, (w3, w4)) = particularSolution(Set(), t2, c2, d2)
    checkSameExpr(toExpr(e2), bi(0), pre2, Map(x.id -> w3, y.id -> w4))
  }

  test("particularSolution preprocess") { implicit ctx =>
    def toExpr(es: Array[Expr], vs: Array[Expr]): Expr = {
      val vars: Array[Expr] = Array[Expr](bi(1)) ++ vs
      es.zip(vars).foldLeft[Expr](bi(0))( (acc: Expr, p: (Expr, Expr)) => Plus(acc, Times(p._1, p._2)) )
    }

    val t1: Expr = Plus(aa, bb)
    val c1: Expr = bi(4)
    val d1: Expr = bi(22)
    val e1: Array[Expr] = Array(t1, c1, d1)
    val (pre1, s1) = particularSolution(Set(aa.id, bb.id), e1.toList)
    checkSameExpr(toExpr(e1, Array(x, y)), bi(0), pre1, Array(x.id, y.id).zip(s1).toMap)

    val t2: Expr = Plus(aa, bb)
    val c2: Expr = bi(4)
    val d2: Expr = bi(22)
    val f2: Expr = bi(10)
    val e2: Array[Expr] = Array(t2, c2, d2, f2)
    val (pre2, s2) = particularSolution(Set(aa.id, bb.id), e2.toList)
    checkSameExpr(toExpr(e2, Array(x, y, z)), bi(0), pre2, Array(x.id, y.id, z.id).zip(s2).toMap)

    val t3: Expr = Plus(aa, Times(bi(2), bb))
    val c3: Expr = bi(6)
    val d3: Expr = bi(24)
    val f3: Expr = bi(9)
    val e3: Array[Expr] = Array(t3, c3, d3, f3)
    val (pre3, s3) = particularSolution(Set(aa.id, bb.id), e3.toList)
    checkSameExpr(toExpr(e3, Array(x, y, z)), bi(0), pre3, Array(x.id, y.id, z.id).zip(s3).toMap)

    val t4: Expr = Plus(aa, bb)
    val c4: Expr = bi(4)
    val e4: Array[Expr] = Array(t4, c4)
    val (pre4, s4) = particularSolution(Set(aa.id, bb.id), e4.toList)
    checkSameExpr(toExpr(e4, Array(x)), bi(0), pre4, Array(x.id).zip(s4).toMap)
  }


  test("linearSet") { implicit ctx =>
    val as = Set[Identifier]()

    val evaluator = new DefaultEvaluator(ctx, Program.empty)

    val eq1 = Array[BigInt](3, 4, 8)
    val basis1 = linearSet(evaluator, as, eq1)
    checkVectorSpace(basis1, eq1)

    val eq2 = Array[BigInt](1, 2, 3)
    val basis2 = linearSet(evaluator, as, eq2)
    checkVectorSpace(basis2, eq2)

    val eq3 = Array[BigInt](1, 1)
    val basis3 = linearSet(evaluator, as, eq3)
    checkVectorSpace(basis3, eq3)

    val eq4 = Array[BigInt](1, 1, 2, 7)
    val basis4 = linearSet(evaluator, as, eq4)
    checkVectorSpace(basis4, eq4)

    val eq5 = Array[BigInt](1, -1)
    val basis5 = linearSet(evaluator, as, eq5)
    checkVectorSpace(basis5, eq5)

    val eq6 = Array[BigInt](1, -6, 3)
    val basis6 = linearSet(evaluator, as, eq6)
    checkVectorSpace(basis6, eq6)
  }


  def enumerate(nbValues: Int, app: (Array[Int] => Unit)) {
    val min = -5
    val max = 5
    val counters: Array[Int] = (1 to nbValues).map(_ => min).toArray
    var i = 0

    while(i < counters.length) {
      app(counters)
      if(counters(i) < max)
        counters(i) += 1
      else {
        while(i < counters.length && counters(i) >= max) {
          counters(i) = min
          i += 1
        }
        if(i < counters.length) {
          counters(i) += 1
          i = 0
        }
      }
    }

  }

  //TODO: automatic check result
  test("elimVariable") { implicit ctx =>
    val as = Set[Identifier](aa.id, bb.id)

    val evaluator = new DefaultEvaluator(ctx, Program.empty)

    def check(t: Expr, c: List[Expr], prec: Expr, witnesses: List[Expr], freshVars: List[Identifier]) {
      enumerate(freshVars.size, (vals: Array[Int]) => {
        val mapping: Map[Expr, Expr] = freshVars.zip(vals.toList).map(t => (Variable(t._1), bi(t._2))).toMap
        val cWithVars: Expr = c.zip(witnesses).foldLeft[Expr](bi(0)){ case (acc, (coef, wit)) => Plus(acc, Times(coef, replace(mapping, wit))) }
        checkSameExpr(Plus(t, cWithVars), bi(0), prec)
      })
    }

    val t1 = Minus(Times(bi(2), aa), bb)
    val c1 = List(bi(3), bi(4), bi(8))
    val (pre1, wit1, f1) = elimVariable(evaluator, as, t1::c1)
    check(t1, c1, pre1, wit1, f1)

    val t2 = Plus(Plus(bi(0), bi(2)), Times(bi(-1), bi(3)))
    val c2 = List(bi(1), bi(-1))
    val (pre2, wit2, f2) = elimVariable(evaluator, Set(), t2::c2)
    check(t2, c2, pre2, wit2, f2)


    val t3 = Minus(Times(bi(2), aa), bi(3))
    val c3 = List(bi(2))
    val (pre3, wit3, f3) = elimVariable(evaluator, Set(aa.id), t3::c3)
    check(t3, c3, pre3, wit3, f3)

    val t4 = Times(bi(2), aa)
    val c4 = List(bi(2), bi(4))
    val (pre4, wit4, f4) = elimVariable(evaluator, Set(aa.id), t4::c4)
    check(t4, c4, pre4, wit4, f4)

    val t5 = Minus(aa, bb)
    val c5 = List(bi(-60), bi(-3600))
    val (pre5, wit5, f5) = elimVariable(evaluator, Set(aa.id, bb.id), t5::c5)
    check(t5, c5, pre5, wit5, f5)

  }

}
