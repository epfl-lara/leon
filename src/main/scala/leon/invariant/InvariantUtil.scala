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

object Stats {
  //stats  
  var totalTime : Long = 0
  var outerIterations = 0
  var innerIterations = 0
  var retries = 0
  
  //per outer iteration statistics
  var cumVCsize : Long = 0
  var maxVCsize : Long = 0
  var cumUIFADTs : Long = 0
  var maxUIFADTs : Long = 0
  var cumTempVars : Long = 0
  var maxTempVars : Long= 0
  
  //per inner iteration stats    
  var cumFarkaSize : Long = 0
  var maxFarkaSize : Long = 0
  var cumFarkaTime : Long = 0
  var maxFarkaTime : Long = 0  
  var cumNLsize : Long = 0
  var maxNLsize : Long = 0
  var cumDijsize : Long = 0
  var maxDijsize : Long = 0
  var cumExploreTime: Long  = 0
  var maxExploreTime: Long  = 0
  var cumCompatCalls : Long = 0
  var maxCompatCalls : Long = 0
  var cumElimVars: Long  = 0
  var maxElimVars: Long  = 0
  var cumElimAtoms: Long  = 0
  var maxElimAtoms: Long  = 0  
  var cumLemmaApps: Long = 0
  var maxLemmaApps: Long  = 0
  
  var output : String = ""
    
  def addOutput(out : String) = {
    output += out + "\n"
  }
  
  def cumMax(cum : Long, max: Long, newval : Long) : (Long,Long) = {    
    (cum + newval, if(max < newval) newval else max)
  }
  
  def dumpStats(pr : PrintWriter) ={
    //outer iteration statistics
    pr.println("Total Time: "+(totalTime/1000.0)+"s")
    pr.println("VC refinements : "+outerIterations)
    pr.println("Disjunct Explorations : "+innerIterations)
    pr.println("Avg VC size : "+ (cumVCsize.toDouble / outerIterations))
    pr.println("Max VC size : "+maxVCsize)
    pr.println("Avg UIF-ADT size : "+ (cumUIFADTs.toDouble / outerIterations))
    pr.println("Max UIF-ADT size : "+ maxUIFADTs)        
    pr.println("avgTempVars : "+(cumTempVars.toDouble / outerIterations))
    pr.println("maxTempVars : "+maxTempVars)
    pr.println("Total retries: "+retries)    
    
    //inner iteration statistics
    pr.println("avgFarkaSize : "+(cumFarkaSize.toDouble / innerIterations))
    pr.println("maxFarkaSize : "+maxFarkaSize)
    pr.println("avgFarkaTime : "+((cumFarkaTime.toDouble / innerIterations))/1000.0 +"s")
    pr.println("maxFarkaTime : "+(maxFarkaTime)/1000.0+"s")
    pr.println("avgNLSize : "+(cumNLsize.toDouble / innerIterations))
    pr.println("maxNLSize : "+maxNLsize)           
    pr.println("avgDijSize : "+(cumDijsize.toDouble / innerIterations))
    pr.println("maxDijSize : "+maxDijsize)
    pr.println("avgElimvars : "+(cumElimVars.toDouble / innerIterations))
    pr.println("maxElimvars : "+maxElimVars)
    pr.println("avgElimAtoms : "+(cumElimAtoms.toDouble / innerIterations))
    pr.println("maxElimAtoms : "+maxElimAtoms)
    pr.println("avgExploreTime : "+((cumExploreTime.toDouble / innerIterations))/1000.0 +"s")
    pr.println("maxExploreTime : "+maxExploreTime/1000.0+"s")
    pr.println("avgCompatCalls : "+(cumCompatCalls.toDouble / innerIterations))
    pr.println("maxCompatCalls : "+maxCompatCalls)
    pr.println("avgLemmaApps : "+(cumLemmaApps.toDouble / innerIterations))
    pr.println("maxLemmaApps : "+maxLemmaApps)
    
    pr.println("########## Outputs ############")
    pr.println(output)
    pr.flush()    
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

object TempIdFactory {
  
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
