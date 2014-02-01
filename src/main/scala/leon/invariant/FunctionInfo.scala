package leon
package invariant

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._

class FunctionInfo(val fundef : FunDef) {
  var template : Option[Expr] = None
  var isMonotonic : Boolean = false
  //TODO: handle monotonicity in the presence of time etc.
  //Provide ways for specifying other lemmas about a function
  //more information to be added here
  var isTheoryOperation = false
}

object FunctionInfoFactory {

  var functionInfos = Map[FunDef,FunctionInfo]()
  
  /**
   * Sets a new template for the functions
   */
  def setTemplate(fd:FunDef, tempExpr :Expr) = {
    
    val funinfo = functionInfos.getOrElse(fd, { 
      val info = new FunctionInfo(fd)
      functionInfos += (fd -> info)
      info
    })
    if(!funinfo.template.isDefined)
    	funinfo.template = Some(tempExpr) 
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
  
  def templateMap : Map[FunDef, Expr] = {
    functionInfos.collect {
      case pair@_ if pair._2.template.isDefined => (pair._1 -> pair._2.template.get)                   
    }
  }
  
  def isMonotonic(fd: FunDef ) ={ 
    if(functionInfos.contains(fd)) {
      val info = functionInfos(fd)
      info.isMonotonic
    } else false
  }  
  
  def getOrMakeInfo(fd: FunDef) : FunctionInfo = {
    functionInfos.getOrElse(fd, { 
      val info = new FunctionInfo(fd)
      functionInfos += (fd -> info)
      info
    })
  }
  
  def setMonotonicity(fd: FunDef) = {
    val funinfo = getOrMakeInfo(fd) 
    funinfo.isMonotonic = true 
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
}