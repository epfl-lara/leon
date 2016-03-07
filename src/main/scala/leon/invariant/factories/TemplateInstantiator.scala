/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.factories

import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import invariant.util._
import invariant.structure._
import invariant.engine.InferenceContext
import leon.solvers.Model
import leon.invariant.util.RealValuedExprEvaluator
import PredicateUtil._
import FunctionUtils._
import ExpressionTransformer._

object TemplateInstantiator {

  /**
   * Computes the invariant for all the procedures given a model for the template variables.
   * (Undone) If the mapping does not have a value for an id, then the id is bound to the simplest value
   */
  def getAllInvariants(model: Model, funs: Seq[FunDef], prettyInv: Boolean = false): Map[FunDef, Expr] = {
    val invs = funs.collect {
      case fd if fd.hasTemplate =>
        (fd, instantiateNormTemplates(model, fd.normalizedTemplate.get, prettyInv))
    }.toMap
    invs
  }

  /**
   * This function expects a template in a normalized form.
   */
  def instantiateNormTemplates(model: Model, template: Expr, prettyInv: Boolean = false): Expr = {
    val tempvars = getTemplateVars(template)
    val instTemplate = instantiate(template, tempvars.map { v => (v, model(v.id)) }.toMap, prettyInv)
    unflatten(instTemplate)
  }

  /**
   * Instantiates templated subexpressions of the given expression (expr) using the given mapping for the template variables.
   * The instantiation also takes care of converting the rational coefficients to integer coefficients.
   */
  def instantiate(expr: Expr, tempVarMap: Map[Expr, Expr], prettyInv: Boolean = false): Expr = {
    //do a simple post transform and replace the template vars by their values
    val inv = simplePostTransform {
      case tempExpr@(e@Operator(Seq(lhs, rhs), op)) if ((e.isInstanceOf[Equals] || e.isInstanceOf[LessThan]
        || e.isInstanceOf[LessEquals] || e.isInstanceOf[GreaterThan]
        || e.isInstanceOf[GreaterEquals])
        &&
        getTemplateVars(tempExpr).nonEmpty) => {
        val linearTemp = LinearConstraintUtil.exprToTemplate(tempExpr)
        instantiateTemplate(linearTemp, tempVarMap, prettyInv)
      }
      case tempExpr => tempExpr
    }(expr)
    inv
  }

  def validateLiteral(e: Expr) = e match {
    case FractionalLiteral(num, denom) => {
      if (denom == 0)
        throw new IllegalStateException("Denominator is zero !! " + e)
      if (denom < 0)
        throw new IllegalStateException("Denominator is negative: " + denom)
      true
    }
    case IntLiteral(_)             => true
    case InfiniteIntegerLiteral(_) => true
    case _                         => throw new IllegalStateException("Not a real literal: " + e)
  }

  def instantiateTemplate(linearTemp: LinearTemplate, tempVarMap: Map[Expr, Expr], prettyInv: Boolean = false): Expr = {
    val bigone = BigInt(1)
    val coeffMap = linearTemp.coeffTemplate.map((entry) => {
      val (term, coeffTemp) = entry
      val coeffE = replace(tempVarMap, coeffTemp)
      val coeff = RealValuedExprEvaluator.evaluate(coeffE)

      validateLiteral(coeff)

      (term -> coeff)
    })
    val const = if (linearTemp.constTemplate.isDefined) {
      val constE = replace(tempVarMap, linearTemp.constTemplate.get)
      val constV = RealValuedExprEvaluator.evaluate(constE)

      validateLiteral(constV)
      Some(constV)
    } else None

    val realValues: Seq[Expr] = coeffMap.values.toSeq ++ { if (const.isDefined) Seq(const.get) else Seq() }
    //the coefficients could be fractions ,so collect all the denominators
    val getDenom = (t: Expr) => t match {
      case FractionalLiteral(num, denum) => denum
      case _                             => bigone
    }

    val denoms = realValues.foldLeft(Set[BigInt]())((acc, entry) => { acc + getDenom(entry) })

    //compute the LCM of the denominators
    val gcd = denoms.foldLeft(bigone)((acc, d) => acc.gcd(d))
    val lcm = denoms.foldLeft(BigInt(1))((acc, d) => {
      val product = (acc * d)
      if (product % gcd == 0)
        product / gcd
      else product
    })

    //scale the numerator by lcm
    val scaleNum = (t: Expr) => t match {
      case FractionalLiteral(num, denum) =>
        InfiniteIntegerLiteral(num * (lcm / denum))
      case InfiniteIntegerLiteral(n) =>
        InfiniteIntegerLiteral(n * lcm)
      case _ => throw new IllegalStateException("Coefficient not assigned to any value")
    }
    val intCoeffMap = coeffMap.map((entry) => (entry._1, scaleNum(entry._2)))
    val intConst = if (const.isDefined) Some(scaleNum(const.get)) else None

    val linearCtr = new LinearConstraint(linearTemp.op, intCoeffMap, intConst)
    if (prettyInv)
      linearCtr.toPrettyExpr
    else linearCtr.toExpr
  }
}