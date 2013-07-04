package leon
package invariant

import z3.scala._
import purescala.DataStructures._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import solvers.{ Solver, TrivialSolver, TimeoutSolver }
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

trait Template { 
}
/**
 * Class representing linear templates which is a constraint of the form 
 * a1*v1 + a2*v2 + .. + an*vn + a0 <= 0 or = 0 or < 0 where ai's are unknown coefficients 
 * which could be any arbitrary expression with template variables as free variables
 * and vi's are variables.
 */
class LinearTemplate(val oper: (Expr,Expr) => Expr,
    coeffTemp : Map[Expr, Expr],
    val constTemp: Option[Expr]) extends Template {

  val zero = IntLiteral(0)

  val op = {
     oper
  }
  val coeffTemplate = {
    //assert if the coefficients are templated expressions
    assert(coeffTemp.values.foldLeft(true)((acc, e) => {
      acc && InvariantUtil.isTemplateExpr(e)
    }))
    
    //print the template mapping
    /*println("Coeff Mapping: "+coeffTemp)
    println("Constant: "+constTemplate)*/
    coeffTemp
  }

  val constTemplate  = {
    assert(constTemp match {
      case None => true
      case Some(e) => InvariantUtil.isTemplateExpr(e)
    })
    constTemp
  }

  val template = {
     //construct the expression corresponding to the template here
     var lhs = coeffTemp.foldLeft(null: Expr)((acc, entry) => {
	   val (term, coeff) = entry
	   val minterm = Times(coeff,term)
	   if(acc == null) minterm else Plus(acc,minterm)
     })
     lhs = if(constTemp.isDefined){
	       if(lhs == null) constTemp.get
	       else Plus(lhs,constTemp.get) 
	   } else lhs		
     val expr = oper(lhs,zero)
     assert(expr.isInstanceOf[Equals] || expr.isInstanceOf[LessThan] || expr.isInstanceOf[GreaterThan]
		|| expr.isInstanceOf[LessEquals]|| oper == expr.isInstanceOf[GreaterEquals])
     expr
  }        

  def templateVars : Set[Variable]  = {
    InvariantUtil.getTemplateVars(template)
  }
		
  def coeffEntryToString(coeffEntry: (Expr, Expr)): String = {
    val (e, i) = coeffEntry
    i match {
      case IntLiteral(1) => e.toString
      case IntLiteral(-1) => "-" + e.toString
      case IntLiteral(v) => v + e.toString
      case _ => i + " * " + e.toString
    }
  }

  override def toString(): String = {

    val coeffStr = if (coeffTemplate.isEmpty) ""
    else {
      val (head :: tail) = coeffTemplate.toList
      tail.foldLeft(coeffEntryToString(head))((str, pair) => {

        val termStr = coeffEntryToString(pair)
        (str + " + " + termStr)
      })
    }
    val constStr = if (constTemplate.isDefined) constTemplate.get.toString else ""
    val str = if(!coeffStr.isEmpty() && !constStr.isEmpty()) coeffStr + " + "+ constStr
    			else coeffStr + constStr
    str + (template match {
        case t: Equals => " = "
        case t: LessThan => " < "
        case t: GreaterThan => " > "
        case t: LessEquals => " <= "
        case t: GreaterEquals => " >= "
      }) + "0"    
  }

  override def hashCode(): Int = {
    template.hashCode()
  }

  override def equals(obj: Any): Boolean = obj match {
    case lit: LinearTemplate => {
      if (!lit.template.equals(this.template)) {
        //println(lit.template + " and " + this.template+ " are not equal ")
        false
      } else true
    }
    case _ => false
  }  
}

/**
 * class representing a linear constraint. This is a linear template wherein the coefficients are constants
 */
class LinearConstraint(val opr: (Expr,Expr) => Expr, cMap: Map[Expr, Expr], val constant: Option[Expr])
  extends LinearTemplate(opr, cMap, constant) {
  
  val coeffMap = {
    //assert if the coefficients are only constant expressions
    assert(cMap.values.foldLeft(true)((acc, e) => {
      acc && variablesOf(e).isEmpty
    }))
    
    //TODO: here we should try to simplify reduce the constant expressions    
    cMap
  }

  def expr : Expr = template
}

class BoolConstraint(val e : Expr) extends Template {
  val expr = {
    assert(e match{ 
      case Variable(_) => true
      case Not(Variable(_)) => true
      case _ => false
      })
    e
  }

  override def toString(): String = {
    expr.toString
  }
}

class ADTConstraint(val e: Expr) extends Template {

  val expr = {
    assert(e match {
      case Iff(v@Variable(_),ci@CaseClassInstanceOf(_,_)) => true
      case Equals(v@Variable(_),cs@CaseClassSelector(_,_,_)) => true
      case Equals(lhs@Variable(_),rhs@Variable(_)) if(lhs.getType != Int32Type && lhs.getType != RealType) => true
      case Not(Equals(lhs@Variable(_),rhs@Variable(_))) if(lhs.getType != Int32Type && lhs.getType != RealType) => true
      case _ => false
    })
    e
  }

  override def toString(): String = {
    expr.toString
  }
}
