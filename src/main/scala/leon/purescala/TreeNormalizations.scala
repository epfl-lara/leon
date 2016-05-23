/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import Common._
import Types._
import Expressions._
import ExprOps._

object TreeNormalizations {

  /* TODO: we should add CNF and DNF at least */

  case class NonLinearExpressionException(msg: String) extends Exception

  //assume the function is an arithmetic expression, not a relation
  //return a normal form where the [t a1 ... an] where
  //expr = t + a1*x1 + ... + an*xn and xs = [x1 ... xn]
  //do not keep the evaluation order
  def linearArithmeticForm(expr: Expr, xs: Array[Identifier]): Array[Expr] = {

    //assume the expr is a literal (mult of constants and variables) with degree one
    def extractCoef(e: Expr): (Expr, Identifier) = {
      var id: Option[Identifier] = None
      var coef: BigInt = 1

      def rec(e: Expr): Unit = e match {
        case InfiniteIntegerLiteral(i) => coef = coef*i
        case Variable(id2) => if(id.isEmpty) id = Some(id2) else throw NonLinearExpressionException("multiple variable")
        case Times(e1, e2) => rec(e1); rec(e2)
      }

      rec(e)
      assert(id.isDefined)
      (InfiniteIntegerLiteral(coef), id.get)
    }


    def containsId(e: Expr, id: Identifier): Boolean = e match {
      case Times(e1, e2) => containsId(e1, id) || containsId(e2, id)
      case InfiniteIntegerLiteral(_) => false
      case Variable(id2) => id == id2
      case err => throw NonLinearExpressionException("unexpected in containsId: " + err)
    }

    def group(es: Seq[Expr], id: Identifier): Expr = {
      val totalCoef = es.foldLeft(BigInt(0))((acc, e) => {
        val (InfiniteIntegerLiteral(i), id2) = extractCoef(e)
        assert(id2 == id)
        acc + i
      })
      Times(InfiniteIntegerLiteral(totalCoef), Variable(id))
    }

    var exprs: Seq[Expr] = expandedForm(expr)
    val res: Array[Expr] = new Array(xs.length + 1)

    xs.zipWithIndex.foreach{case (id, index) => {
      val (terms, rests) = exprs.partition(containsId(_, id))
      exprs = rests
      val Times(coef, Variable(_)) = group(terms, id)
      res(index+1) = coef
    }}

    res(0) = simplifyArithmetic(exprs.foldLeft[Expr](InfiniteIntegerLiteral(0))(Plus))
    res
  }

  //multiply two sums together and distribute in a larger sum
  //do not keep the evaluation order
  def multiply(es1: Seq[Expr], es2: Seq[Expr]): Seq[Expr] = {
    for {
      e1 <- es1
      e2 <- es2
    } yield Times(e1,e2)
  }

  //expand the expr in a sum of "atoms", each atom being a product of literal and variable
  //do not keep the evaluation order
  def expandedForm(expr: Expr): Seq[Expr] = expr match {
    case Plus(es1, es2) => expandedForm(es1) ++ expandedForm(es2)
    case Minus(e1, e2) => expandedForm(e1) ++ expandedForm(e2).map(Times(InfiniteIntegerLiteral(-1), _): Expr)
    case UMinus(e) => expandedForm(e).map(Times(InfiniteIntegerLiteral(-1), _): Expr)
    case Times(es1, es2) => multiply(expandedForm(es1), expandedForm(es2))
    case v@Variable(_) if v.getType == IntegerType => Seq(v)
    case n@InfiniteIntegerLiteral(_) => Seq(n)
    case err => throw NonLinearExpressionException("unexpected in expandedForm: " + err)
  }

}
