package leon.synthesis.condabd
package ranking

import leon.purescala.Trees._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.TypeTrees._
import leon.purescala.TreeOps

import insynth.reconstruction.Output
import _root_.insynth.structures.Weight._
import _root_.insynth.util.logging.HasLogger

object Candidate {  
  private var _freshResultVariable: Identifier = _
  def freshResultVariable = _freshResultVariable
  
  def getFreshResultVariable(tpe: TypeTree) = _freshResultVariable = FreshIdentifier("result", true).setType(tpe)
  
  def makeDefaultCandidates(candidatePairs: IndexedSeq[Output], bodyBuilder: Expr => Expr, tfd: TypedFunDef) = {
    getFreshResultVariable(tfd.returnType)
    candidatePairs map {
      pair =>
      	DefaultCandidate(pair.getSnippet, bodyBuilder(pair.getSnippet), pair.getWeight, tfd)
    }
  }
  
  def makeCodeGenCandidates(candidatePairs: IndexedSeq[Output], bodyBuilder: Expr => Expr, tfd: TypedFunDef) = {
    getFreshResultVariable(tfd.returnType)
    candidatePairs map {
      pair =>
      	CodeGenCandidate(pair.getSnippet, bodyBuilder(pair.getSnippet), pair.getWeight, tfd)
    }
  }
}

abstract class Candidate(weight: Weight) {
  def getExpr: Expr
  
  def prepareExpression: Expr
  
  def getWeight = weight
}

case class DefaultCandidate(expr: Expr, bodyExpr: Expr, weight: Weight, tfd: TypedFunDef)
	extends Candidate(weight) with HasLogger {
  import Candidate._
    
  override def getExpr = expr

  lazy val expressionToEvaluate = {
    import TreeOps._
    
    assert(bodyExpr.getType != Untyped)
    val resFresh = freshResultVariable//.setType(expr.getType)

    val (id, post) = tfd.postcondition.get

    // body can contain (self-)recursive calls
    Let(resFresh, bodyExpr,
      replace(Map(Variable(id) -> Variable(resFresh)),
        matchToIfThenElse(post)))
  }
  
  override def prepareExpression = {
    // set appropriate body to the function for the correct evaluation due to recursive calls
    tfd.fd.body = Some(bodyExpr)
    
//    finest("going to evaluate candidate for: " + tfd)
//    finest("going to evaluate candidate for: " + expressionToEvaluate)
    expressionToEvaluate
  }
}

case class CodeGenCandidate(expr: Expr, bodyExpr: Expr, weight: Weight, tfd: TypedFunDef)
	extends Candidate(weight) with HasLogger {
  import Candidate._
    
  override def getExpr = expr

  lazy val (expressionToEvaluate, newFunDef) = {
    import TreeOps._
    val fd = tfd.fd
    
    val newFunId = FreshIdentifier("tempIntroducedFunction")
    val newFun = new FunDef(newFunId, fd.tparams, fd.returnType, fd.params)
    newFun.precondition = fd.precondition
    newFun.postcondition = fd.postcondition
    
    def replaceFunDef(expr: Expr) = expr match {
      case FunctionInvocation(`tfd`, args) =>
        Some(FunctionInvocation(newFun.typed(tfd.tps), args))
      case _ => None
    }
    val newBody = postMap(replaceFunDef)(bodyExpr)
    
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
//    finest("going to evaluate candidate for: " + tfd)
//    finest("going to evaluate candidate for: " + expressionToEvaluate)
    expressionToEvaluate
  }
}
