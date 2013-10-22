package leon
package invariant

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import scala.collection.mutable.{ Set => MutableSet }
import scala.collection.immutable.Stack
import leon.evaluators._
import java.io._
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
import leon.invariant._
import scala.collection.mutable.{Set => MutableSet}
import java.io._

object FileCountGUID {
	 var fileCount = 0
}

//three valued logic
object TVL {
  abstract class Value 
  object FALSE extends Value
  object TRUE extends Value
  object MAYBE extends Value
}

case class Call(retexpr: Expr, fi: FunctionInvocation) {
  val expr = Equals(retexpr,fi)   
}

//this is used as a place hold result variable if not other result variable is specified
case class ResultVariable() extends Expr with Terminal {
  override def toString : String = "#res"
}


object InvariantUtil {
  
  val zero = IntLiteral(0)
  val one = IntLiteral(1)

  //compute the formal to the actual argument mapping   
  /*def formalToAcutal(call : Call, resvar : Expr) : Map[Expr, Expr] = {    
    val argmap: Map[Expr, Expr] = Map(resvar -> call.retexpr) ++ call.fi.funDef.args.map(_.id.toVariable).zip(call.fi.args)
    argmap
  }*/
  
  def getFunctionReturnVariable(fd: FunDef) = {
    if(fd.hasPostcondition) fd.postcondition.get._1.toVariable
    else ResultVariable().setType(fd.returnType)
  }
  
  def formalToAcutal(call : Call) : Map[Expr, Expr] = {
    val fd = call.fi.funDef
    val resvar =getFunctionReturnVariable(fd) 
    val argmap: Map[Expr, Expr] = Map(resvar -> call.retexpr) ++ fd.args.map(_.id.toVariable).zip(call.fi.args)
    argmap
  }
  
  /**
   * Checks if the input expression has only template variables as free variables
   */
  def isTemplateExpr(expr : Expr) :Boolean ={
    var foundVar = false    
    simplePostTransform((e : Expr) => e match {    
      case Variable(id) => { 
        if(!TemplateIdFactory.IsTemplateIdentifier(id))
          foundVar = true
        e
      }
      case ResultVariable() => {
	     foundVar = true
	     e
      }
      case _ => e
    })(expr)
    
    !foundVar
  }
  
  def getTemplateVars(expr: Expr) : Set[Variable] = {
    var tempVars = Set[Variable]()    
    simplePostTransform((e : Expr) => e match {
      case t@Variable(id) => {
        if(TemplateIdFactory.IsTemplateIdentifier(id))
        	tempVars += t
        e       
      }
      case _ => e
    })(expr)
    
    tempVars
  }

  /**
   * Checks if the expression has real valued sub-expressions.
   */
  def hasReals(expr : Expr) : Boolean = {
    var foundReal = false
    simplePostTransform((e :Expr) => e match {
      case _ => { 
        if(e.getType == RealType) 
          foundReal = true;
        e      
      }    		  	
    })(expr)
    foundReal
  }
  
  
  def fix[A](f: (A) => A)(a: A): A = {
      val na = f(a)
      if(a == na) a else fix(f)(na)
  }

  /**
   * Convert body to a relation
   */
  //def convertToRel(body: Expr): (Expr, Variable) = {
    //freshen the body
    //val freshBody = matchToIfThenElse(freshenLocals(body))
    //val resFresh = Variable(FreshIdentifier("result", true).setType(freshBody.getType))
    //println("Rel Body: "+Equals(resFresh, freshBody))
    //val bodyExpr = ExpressionTransformer.normalizeExpr(Equals(resFresh, freshBody))
    /*(bodyExpr, resFresh)
  }*/
  
  def atomNum(e : Expr) : Int = {
    var count : Int = 0
    simplePostTransform((e : Expr) => e match {
      case And(args) => {
        count += args.size
        e
      }         
      case Or(args) => {
        count += args.size
        e
      }
      case _ => e
    })(e)
    count
  } 
  
  def isCallExpr(e: Expr) : Boolean = e match {
    case Equals(Variable(_),FunctionInvocation(_,_)) => true
    case _ => false
  }
  
  /*def getLHS(e: Expr) : Expr = e match {
    case Equals(r@Variable(_),FunctionInvocation(_,_)) => r
    case _ => throw new IllegalStateException("not a call expression")
  }*/
  
  def isSelector(e: Expr) : Boolean = e match {
    case Equals(Variable(_),CaseClassSelector(_,_,_)) => true
    case Equals(Variable(_),TupleSelect(_,_)) => true
    case _ => false
  }
}
