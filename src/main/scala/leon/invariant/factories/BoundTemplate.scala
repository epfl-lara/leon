package leon
package invariant.factories

import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import java.io._

/**
 * This template generator creates a bound template for the result of a function if it returns an integer value
 */
/*class BoundTemplate(prog: Program, reporter: Reporter) extends TemplateGenerator {

  private val zero = InfiniteIntegerLiteral(0)
  var attempt = 0

  def getNextTemplate(fd: FunDef): Expr = {
    //first time ?
    if(attempt <= 0){
      attempt += 1
      //checks if there exists an upper or lower bound
      val boundTemp = if (fd.returnType == IntegerType) {
        val retTerm = InvariantUtil.getFunctionReturnVariable(fd)
        val argTerms = fd.args.filter((vardecl) => vardecl.tpe == IntegerType).map(_.toVariable)
        val rhs = argTerms.foldLeft(TemplateIdFactory.freshTemplateVar(): Expr)((acc, t) => {
          Plus(Times(TemplateIdFactory.freshTemplateVar(), t), acc)
        })
        val retCoeff = TemplateIdFactory.freshTemplateVar()

        And(LessEquals(Times(retCoeff,retTerm), rhs),Not(Equals(retCoeff,zero)))
      } else {
        LessEquals(TemplateIdFactory.freshTemplateVar(), InfiniteIntegerLiteral(0))
      }
      boundTemp
    } else {
      //this should have a solution
      LessEquals(TemplateIdFactory.freshTemplateVar(), InfiniteIntegerLiteral(0))
    }
  }
}*/