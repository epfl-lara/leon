package lesynth
package ranking

import leon.purescala.Trees._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.TypeTrees._
import leon.purescala.TreeOps

import insynth.reconstruction.Output
import insynth.structures.Weight._
import insynth.util.logging.HasLogger

object Candidate {  
  private var _freshResultVariable: Identifier = _
  def freshResultVariable = _freshResultVariable
  
  def getFreshResultVariable(tpe: TypeTree) = _freshResultVariable = FreshIdentifier("result", true).setType(tpe)
  
  def makeDefaultCandidates(candidatePairs: IndexedSeq[Output], bodyBuilder: Expr => Expr, funDef: FunDef) = {
    getFreshResultVariable(funDef.body.get.getType)
    candidatePairs map {
      pair =>
      	DefaultCandidate(pair.getSnippet, bodyBuilder(pair.getSnippet), pair.getWeight, funDef)
    }
  }
  
  def makeCodeGenCandidates(candidatePairs: IndexedSeq[Output], bodyBuilder: Expr => Expr, funDef: FunDef) = {
    getFreshResultVariable(funDef.body.get.getType)
    candidatePairs map {
      pair =>
      	CodeGenCandidate(pair.getSnippet, bodyBuilder(pair.getSnippet), pair.getWeight, funDef)
    }
  }
}

abstract class Candidate(weight: Weight) {
  def getExpr: Expr
  
  def prepareExpression: Expr
  
  def getWeight = weight
}

case class DefaultCandidate(expr: Expr, bodyExpr: Expr, weight: Weight, holeFunDef: FunDef)
	extends Candidate(weight) with HasLogger {
  import Candidate._
    
  override def getExpr = expr

  lazy val expressionToEvaluate = {
    import TreeOps._
    
    assert(bodyExpr.getType != Untyped)
    val resFresh = freshResultVariable//.setType(expr.getType)

    val (id, post) = holeFunDef.postcondition.get

    // body can contain (self-)recursive calls
    Let(resFresh, bodyExpr,
      replace(Map(Variable(id) -> Variable(resFresh)),
        matchToIfThenElse(post)))
  }
  
  override def prepareExpression = {
    // set appropriate body to the function for the correct evaluation due to recursive calls
    holeFunDef.body = Some(bodyExpr)
    
//    finest("going to evaluate candidate for: " + holeFunDef)
//    finest("going to evaluate candidate for: " + expressionToEvaluate)
    expressionToEvaluate
  }
}

case class CodeGenCandidate(expr: Expr, bodyExpr: Expr, weight: Weight, holeFunDef: FunDef)
	extends Candidate(weight) with HasLogger {
  import Candidate._
    
  override def getExpr = expr

  lazy val (expressionToEvaluate, newFunDef) = {
    import TreeOps._
    
    val newFunId = FreshIdentifier("tempIntroducedFunction")
    val newFun = new FunDef(newFunId, holeFunDef.returnType, holeFunDef.args)
    newFun.precondition = holeFunDef.precondition
    newFun.postcondition = holeFunDef.postcondition
    
    def replaceFunDef(expr: Expr) = expr match {
      case FunctionInvocation(`holeFunDef`, args) =>
        Some(FunctionInvocation(newFun, args))
      case _ => None
    }
    val newBody = searchAndReplace(replaceFunDef)(bodyExpr)
    
    newFun.body = Some(newBody)
    
    assert(bodyExpr.getType != Untyped)
    val resFresh = freshResultVariable//.setType(expr.getType)

    val (id, post) = newFun.postcondition.get

    // body can contain (self-)recursive calls
    (Let(resFresh, newBody,
      replace(Map(Variable(id) -> Variable(resFresh)),
        matchToIfThenElse(post)))
    ,
    newFun)
  }
  
  override def prepareExpression = {
//    finest("going to evaluate candidate for: " + holeFunDef)
//    finest("going to evaluate candidate for: " + expressionToEvaluate)
    expressionToEvaluate
  }
}
