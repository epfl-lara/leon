package leon.synthesis

import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.Common._

object ArithmeticNormalization {

  //assume the function is an arithmetic expression, not a relation
  //return a normal form where the [t a1 ... an] where
  //expr = t + a1*x1 + ... + an*xn and xs = [x1 ... xn]
  def apply(expr: Expr, xs: Array[Identifier]): Array[Expr] = {

    def containsId(e: Expr, id: Identifier): Boolean = e match {
      case Times(e1, e2) => containsId(e1, id) || containsId(e2, id)
      case IntLiteral(_) => false
      case Variable(id2) => id == id2
      case _ => sys.error("unexpected format")
    }

    def group(es: Seq[Expr], id: Identifier): Expr = {
      val totalCoef = es.foldLeft(0)((acc, e) => {
        val (IntLiteral(i), id2) = extractCoef(e)
        assert(id2 == id)
        acc + i
      })
      Times(IntLiteral(totalCoef), Variable(id))
    }

    var expandedForm: Seq[Expr] = expand(expr)
    val res: Array[Expr] = new Array(xs.size + 1)

    xs.zipWithIndex.foreach{case (id, index) => {
      val (terms, rests) = expandedForm.partition(containsId(_, id))
      expandedForm = rests
      val Times(coef, Variable(_)) = group(terms, id)
      res(index+1) = coef
    }}

    res(0) = expandedForm.foldLeft[Expr](IntLiteral(0))(Plus(_, _))
    res
  }


  //assume the expr is a literal (mult of constants and variables) with degree one
  def extractCoef(e: Expr): (Expr, Identifier) = {
    var id: Option[Identifier] = None
    var coef = 1

    def rec(e: Expr): Unit = e match {
      case IntLiteral(i) => coef = coef*i
      case Variable(id2) => if(id.isEmpty) id = Some(id2) else sys.error("multiple variables")
      case Times(e1, e2) => rec(e1); rec(e2)
    }

    rec(e)
    assert(!id.isEmpty)
    (IntLiteral(coef), id.get)
  }

  //multiply two sums together and distribute in a bigger sum
  def multiply(es1: Seq[Expr], es2: Seq[Expr]): Seq[Expr] = {
    es1.flatMap(e1 => es2.map(e2 => Times(e1, e2)))
  }


  def expand(expr: Expr): Seq[Expr] = expr match {
    case Plus(es1, es2) => expand(es1) ++ expand(es2)
    case Minus(e1, e2) => Times(IntLiteral(-1), e2) +: expand(e1)
    case Times(es1, es2) => multiply(expand(es1), expand(es2))
    case v@Variable(_) => Seq(v)
    case n@IntLiteral(_) => Seq(n)
    case _ => sys.error("Unexpected")
  }


}
