package leon
package invariant.structure

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._

/**
 * Can all of this be made vals ?
 */
class FunctionInfo(val fundef: FunDef) {
  //expressions
  private var template: Option[Expr] = None
  private var timeexpr: Option[Expr] = None
  private var depthexpr: Option[Expr] = None

  //flags
  private var isTheoryOperation = false
  private var isMonotonic: Boolean = false
  private var isCommutative: Boolean = false
  private var isDistributive: Boolean = false

  /**
   * creates a new function info object by
   * (a) copying the flags to the passed object
   * (b) copying the expressions part to the passed object
   * after transforming it using the passed function
   */
  def copyFuncInfo(fd: FunDef, transform: (Expr => Expr)) : FunctionInfo = {
    val newinfo = new FunctionInfo(fd)
    //copying flags
    newinfo.isTheoryOperation = isTheoryOperation
    newinfo.isMonotonic = isMonotonic
    newinfo.isCommutative = isCommutative
    newinfo.isDistributive = isDistributive

    //copying expr state
    newinfo.template = template.map(transform)
    newinfo.timeexpr = timeexpr.map(transform)
    newinfo.depthexpr = depthexpr.map(transform)
    newinfo
  }

  def isTheoryOp = isTheoryOperation
  def doesCommute = isCommutative
  def hasMonotonicity = isMonotonic
  def hasDistributivity = isDistributive

  def setTheoryOperation = isTheoryOperation = true
  def setCommutativity = isCommutative = true
  def setMonotonicity = isMonotonic = true
  def setDistributivity = isDistributive = true

  def setTemplate(tempExpr: Expr) = {    
      template = Some(tempExpr)
//    } else
//      throw IllegalStateException("Template already set for function: " + fundef)
  }
  def hasTemplate: Boolean = template.isDefined
  def getTemplate = template.get

  def setTimeexpr(timeexp: Expr) = {
    if (!timeexpr.isDefined) {
      timeexpr = Some(timeexp)
    } else
      throw IllegalStateException("Timeexpr already set for function: " + fundef)
  }
  def hasTimeexpr = timeexpr.isDefined
  def getTimeexpr = timeexpr.get

  def setDepthexpr(dexpr: Expr) = {
    if (!depthexpr.isDefined) depthexpr = Some(dexpr)
    else throw IllegalStateException("Depthexpr already set for function: " + fundef)
  }
  def hasDepthexpr = depthexpr.isDefined
  def getDepthexpr = depthexpr.get
}

object FunctionInfoFactory {

  private var functionInfos = Map[FunDef, FunctionInfo]()

  def getFunctionInfo(fd: FunDef): Option[FunctionInfo] = {
    functionInfos.get(fd)
  }

  def getOrMakeInfo(fd: FunDef): FunctionInfo = {
    functionInfos.getOrElse(fd, {
      val info = new FunctionInfo(fd)
      functionInfos += (fd -> info)
      info
    })
  }

  def templateMap: Map[FunDef, Expr] = {
    functionInfos.collect {
      case pair @ _ if pair._2.hasTemplate => (pair._1 -> pair._2.getTemplate)
    }
  }
  
  def createFunctionInfo(fd: FunDef, transform: (Expr => Expr), from: FunctionInfo): FunctionInfo = {
    val newinfo = from.copyFuncInfo(fd, transform)
    functionInfos += (fd -> newinfo)
    newinfo
  }
}