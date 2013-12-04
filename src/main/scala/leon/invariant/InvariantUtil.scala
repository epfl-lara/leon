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
	 def getID : Int = {
	   var oldcnt = fileCount
	   fileCount += 1
	   oldcnt
	 }
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

//this used to refer to the time steps of a procedure
case class TimeVariable() extends Expr with Terminal with FixedType {
    val fixedType = Int32Type
    override def toString : String = "#time"
}

object TVarFactory {
  
  val temporaries = MutableSet[Identifier]()
  //these are dummy identifiers used in 'CaseClassSelector' conversion 
  val dummyIds = MutableSet[Identifier]()
  
  def createTemp(name : String) : Identifier = {
    val freshid = FreshIdentifier(name,true)
    temporaries.add(freshid)
    freshid
  }
  
  def createDummy() : Identifier ={
    val freshid = FreshIdentifier("dy",true)
    dummyIds.add(freshid)
    freshid
  }
  
  def isTemporary(id: Identifier) : Boolean = temporaries.contains(id)
  def isDummy(id: Identifier) : Boolean = dummyIds.contains(id)  
}

object InvariantUtil {
  
  val zero = IntLiteral(0)
  val one = IntLiteral(1)
  val tru = BooleanLiteral(true)
  
  def getFunctionReturnVariable(fd: FunDef) = {
    if(fd.hasPostcondition) fd.postcondition.get._1.toVariable
    else ResultVariable().setType(fd.returnType)
  }
  
  //compute the formal to the actual argument mapping
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
  
  /**
   * Checks if the expression has real valued sub-expressions.
   * Note: important, <, <=, > etc have be default int type.
   * However, they can also be applied over real arguments
   * So check only if all terminals are real
   */
  def hasInts(expr : Expr) : Boolean = {
    var foundInt = false
    simplePostTransform((e :Expr) => e match {
      case e : Terminal if(e.getType == Int32Type) => {          
        foundInt = true;
        e      
      } 
      case _ => e
    })(expr)
    foundInt
  }
  
  
  def fix[A](f: (A) => A)(a: A): A = {
      val na = f(a)
      if(a == na) a else fix(f)(na)
  }
  
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
    
  def numUIFADT(e : Expr) : Int = {
    var count : Int = 0
    simplePostTransform((e : Expr) => e match {
      case FunctionInvocation(_,_) | CaseClass(_,_) | Tuple(_) => {
        count += 1
        e
      }                     
      case _ => e
    })(e)
    count
  } 
  
  def isCallExpr(e: Expr) : Boolean = e match {
    case Equals(Variable(_),FunctionInvocation(_,_)) => true
    case Iff(Variable(_),FunctionInvocation(_,_)) => true
    case _ => false
  }
  
  
  def isADTConstructor(e: Expr) : Boolean = e match {
    case Equals(Variable(_),CaseClass(_,_)) => true
    case Equals(Variable(_),Tuple(_)) => true
    case _ => false
  }
  
  
  def modelToExpr(model : Map[Identifier,Expr]) : Expr = {    
    model.foldLeft(tru : Expr)((acc, elem) => {
      val (k,v) = elem      
      val eq = Equals(k.toVariable,v)
      if(acc == tru) eq 
      else And(acc,eq)
    })
  } 

  def gcd(x: Int, y : Int) : Int ={
    require(x >=0 && y >= 0)    
    if(x == 0) y 
    else gcd(y % x, x)
  }  
}

/**
 * maps all real valued variables and literals to new integer variables/literals and
 * performs the reverse mapping 
 * 
 */
class RealToInt {
  
  var realToIntId = Map[Identifier, Identifier]()
  var intToRealId = Map[Identifier, Identifier]()
  
  def mapRealToInt(inexpr: Expr): Expr = {   
    val transformer = (e: Expr) => e match {
      case RealLiteral(num,1) => IntLiteral(num)
      case RealLiteral(_,_) => throw IllegalStateException("Real literal with non-unit denominator")
      case v @ Variable(realId) if (v.getType == RealType) => {
        val newId = realToIntId.getOrElse(realId, {
          val freshId = FreshIdentifier(realId.name, true).setType(Int32Type)
          realToIntId += (realId -> freshId)
          intToRealId += (freshId -> realId)
          freshId
        })
        Variable(newId)
      }      
      case _ => e
    }
    simplePostTransform(transformer)(inexpr)
  }
  
  def unmapModel(model: Map[Identifier, Expr]) : Map[Identifier, Expr] = {
     model.map((pair) => {
       val (key,value) = if(intToRealId.contains(pair._1)) {
         (intToRealId(pair._1),
             pair._2 match {
    		   	  case IntLiteral(v) => RealLiteral(v,1)
    		   	  case _ => pair._2
    		   	})            
       } 
       else pair
       (key -> value)
     })
  }  
}
