package leon
package invariant

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._

//TODO: are these fields copied
class FunctionInfo(val fundef : FunDef) {  
  var template : Option[Expr] = None
  var timevar : Option[Expr] = None
  var isTheoryOperation = false
  var isMonotonic : Boolean = false
  var isCommutative : Boolean = false
  var isDistributive: Boolean = false
}

object FunctionInfoFactory {

  var functionInfos = Map[FunDef,FunctionInfo]()
  
  /**
   * Sets a new template for the functions
   */
  def setTemplate(fd:FunDef, tempExpr :Expr, timeexpr: Option[Expr]) = {
    
    val funinfo = functionInfos.getOrElse(fd, { 
      val info = new FunctionInfo(fd)
      functionInfos += (fd -> info)
      info
    })
    if(!funinfo.template.isDefined) {
    	funinfo.template = Some(tempExpr)
    	funinfo.timevar = timeexpr
    }
    else 
    	throw IllegalStateException("Template already set for function: "+fd)
  }
  
  def hasTemplate(fd: FunDef) : Boolean = {
    if(functionInfos.contains(fd)) {
      val info = functionInfos(fd)
      info.template.isDefined
    } else false
  }
  
  def getTemplate(fd: FunDef) : Expr = {
    if(functionInfos.contains(fd)) {
      val info = functionInfos(fd)
      info.template.get
      
    } else throw IllegalStateException("cannot find templates!!")
  }
  
  def getTimevar(fd: FunDef) : Option[Expr] = {
    if(functionInfos.contains(fd)) {
      val info = functionInfos(fd)
      info.timevar      
    } else None
  } 
    
  
  def templateMap : Map[FunDef, Expr] = {
    functionInfos.collect {
      case pair@_ if pair._2.template.isDefined => (pair._1 -> pair._2.template.get)                   
    }
  }
  
  def getOrMakeInfo(fd: FunDef) : FunctionInfo = {
    functionInfos.getOrElse(fd, { 
      val info = new FunctionInfo(fd)
      functionInfos += (fd -> info)
      info
    })
  }
  
  def setTheoryOperation(fd: FunDef) = {
    val funcinfo = getOrMakeInfo(fd)
    funcinfo.isTheoryOperation = true
  }
  
  def isTheoryOperation(fd: FunDef) = {
    if(functionInfos.contains(fd)) {
      val info = functionInfos(fd)
      info.isTheoryOperation
    } else false
  }
  
  def setMonotonicity(fd: FunDef) = {
    val funinfo = getOrMakeInfo(fd) 
    funinfo.isMonotonic = true 
  }
  
  def isMonotonic(fd: FunDef ) ={ 
    if(functionInfos.contains(fd)) {
      val info = functionInfos(fd)
      info.isMonotonic
    } else false
  }
  
  def setCommutativity(fd: FunDef) = {
    val funinfo = getOrMakeInfo(fd) 
    funinfo.isCommutative = true 
  }
  
  def isCommutative(fd: FunDef ) ={ 
    if(functionInfos.contains(fd)) {
      val info = functionInfos(fd)
      info.isCommutative
    } else false
  }
  
  def setDistributivity(fd: FunDef) = {
    val funinfo = getOrMakeInfo(fd) 
    funinfo.isDistributive = true 
  }
  
  def isDistributive(fd: FunDef ) ={ 
    if(functionInfos.contains(fd)) {
      val info = functionInfos(fd)
      info.isDistributive
    } else false
  }
}