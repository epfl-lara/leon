package leon
package invariant

import z3.scala._
import purescala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import solvers.{ Solver, TimeoutSolver }
import solvers.z3.FairZ3Solver
import scala.collection.mutable.{ Set => MutableSet }
import scala.collection.mutable.{ Map => MutableMap }
import leon.evaluators._
import java.io._
import leon.solvers.z3.UninterpretedZ3Solver
import leon.LeonContext
import leon.LeonOptionDef
import leon.LeonPhase
import leon.LeonValueOption
import leon.ListValue
import leon.Reporter
import leon.verification.DefaultTactic
import leon.verification.ExtendedVC
import leon.verification.Tactic
import leon.verification.VerificationReport

object TemplateInstantiator {
    /**
   * Computes the invariant for all the procedures given a mapping for the
   * template variables.
   * (Undone) If the mapping does not have a value for an id, then the id is bound to the simplest value
   */
  def getAllInvariants(model: Map[Identifier, Expr], templates :Map[FunDef, Expr]): Map[FunDef, Expr] = {
    val invs = templates.map((pair) => {
      val (fd, t) = pair
      //flatten the template        
      val freevars = variablesOf(t)
      val template = ExpressionTransformer.FlattenFunction(t)

      val tempvars = InvariantUtil.getTemplateVars(template)
      val tempVarMap: Map[Expr, Expr] = tempvars.map((v) => {
        (v, model(v.id))
      }).toMap

      val instTemplate = instantiate(template, tempVarMap)
      //now unflatten it
      val comprTemp = ExpressionTransformer.unFlatten(instTemplate, freevars)
      (fd, comprTemp)
    })
    invs
  }

  /**
   * Instantiates templated subexpressions of the given expression (expr) using the given mapping for the template variables.
   * The instantiation also takes care of converting the rational coefficients to integer coefficients.
   */
  def instantiate(expr: Expr, tempVarMap: Map[Expr, Expr]): Expr = {
    //do a simple post transform and replace the template vars by their values
    val inv = simplePostTransform((tempExpr: Expr) => tempExpr match {
      case e @ BinaryOperator(lhs, rhs, op) if ((e.isInstanceOf[Equals] || e.isInstanceOf[LessThan]
        || e.isInstanceOf[LessEquals] || e.isInstanceOf[GreaterThan]
        || e.isInstanceOf[GreaterEquals]) 
        && 
        !InvariantUtil.getTemplateVars(tempExpr).isEmpty) => {

        //println("Template Expression: "+tempExpr)
        val linearTemp = LinearConstraintUtil.exprToTemplate(tempExpr)
        instantiateTemplate(linearTemp, tempVarMap)
      }
      case _ => tempExpr
    })(expr)    
    inv
  }
  
  
  def validateLiteral(e : Expr) = e match {
    case RealLiteral(num, denom) => {
      if (denom == 0)
        throw new IllegalStateException("Denominator is zero !! " +e)
      if (denom < 0)
        throw new IllegalStateException("Denominator is negative: " + denom)
      true
    }
    case IntLiteral(_) => true
    case _ => throw new IllegalStateException("Not a real literal: " + e)
  }

  def instantiateTemplate(linearTemp: LinearTemplate, tempVarMap: Map[Expr, Expr]): Expr = {
    val coeffMap = linearTemp.coeffTemplate.map((entry) => {
      val (term, coeffTemp) = entry
      val coeffE = replace(tempVarMap, coeffTemp)
      val coeff = RealValuedExprInterpreter.evaluate(coeffE)

      validateLiteral(coeff)
      
      (term -> coeff)
    })
    val const = if (linearTemp.constTemplate.isDefined){
      val constE = replace(tempVarMap, linearTemp.constTemplate.get)
      val constV = RealValuedExprInterpreter.evaluate(constE)
      
      validateLiteral(constV)      
      Some(constV)
    }      
    else None

    val realValues: Seq[Expr] = coeffMap.values.toSeq ++ { if (const.isDefined) Seq(const.get) else Seq() }
    //the coefficients could be fractions ,so collect all the denominators
    val getDenom = (t: Expr) => t match {
      case RealLiteral(num, denum) => denum
      case _ => 1
    }

    val denoms = realValues.foldLeft(Set[Int]())((acc, entry) => { acc + getDenom(entry) })
    
    //compute the LCM of the denominators
    val gcd = denoms.foldLeft(1)((acc, d) => InvariantUtil.gcd(acc,d))        
    val lcm = denoms.foldLeft(1)((acc, d) => {
      val product = (acc * d)
      if(product % gcd == 0) 
        product/ gcd 
      else product 
    })

    //scale the numerator by lcm
    val scaleNum = (t: Expr) => t match {
      case RealLiteral(num, denum) => IntLiteral(num * (lcm / denum))
      case IntLiteral(n) => IntLiteral(n * lcm)
      case _ => throw IllegalStateException("Coefficient not assigned to any value")
    }
    val intCoeffMap = coeffMap.map((entry) => (entry._1, scaleNum(entry._2)))
    val intConst = if (const.isDefined) Some(scaleNum(const.get)) else None

    val linearCtr = new LinearConstraint(linearTemp.op, intCoeffMap, intConst)
    linearCtr.toExpr
  }
}