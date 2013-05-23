package leon
package invariant

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import scala.collection.mutable.{ Set => MutableSet }
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

class RefinementEngine {
     
  private var currentAbs : Expr = _
  private var headCalls = Set[(Expr,FunctionInvocation)]()
  //private var unrolledFuncs = Set[FunDef]()
  
  def this(vc: Expr, fd: FunDef) = {
    this()
    currentAbs = vc    
    //unrolledFuncs += fd
    headCalls = findHeads(vc)
  }
  
  /**
   * Heads are procedure calls whose target definitions have not been unrolled
   */
  private def findHeads(abs: Expr) : Set[(Expr,FunctionInvocation)] ={
    //initialize head functions
    var heads = Set[(Expr,FunctionInvocation)]()
    simplePostTransform((e: Expr) => e match {
      case eq@Equals(rexp,fi@FunctionInvocation(fd,args)) => {
      //  if(!unrolledFuncs.contains(fi.funDef))
        heads ++= Set((rexp,fi))
        eq 
       }
      case _ => e
    })(abs)
    heads
  }  
  

  /**
   * Returns a set of function invocations, body and post condition pairs.
   * This procedure may refine an existing abstraction.
   * Currently, the refinement happens by unrolling.
   */
  def refineAbstraction(): Seq[((Expr,FunctionInvocation), Option[Expr], Option[Expr])] = {
    //here we unroll the methods in the current abstraction by one step
    
    //update unrolled funcs
    //unrolledFuncs ++= headFuncs.map(_.funDef)
    
    var newheads = Set[(Expr,FunctionInvocation)]()
    val unrolls = headCalls.foldLeft(Seq[((Expr,FunctionInvocation), Option[Expr], Option[Expr])]())((acc, call) => {      
      
      val fi = call._2
      if (fi.funDef.body.isDefined) {
        val body = fi.funDef.getBody
        val resFresh = Variable(FreshIdentifier("result", true).setType(body.getType))
        val bexpr = Equals(resFresh, body)

        val prec = fi.funDef.precondition
        val bodyExpr = if (prec.isEmpty) {
          bexpr
        } else {
          And(matchToIfThenElse(prec.get), bexpr)
        }

        if (!fi.funDef.postcondition.isEmpty) {

          val post = fi.funDef.postcondition
          val postExpr = replace(Map(ResultVariable() -> resFresh), matchToIfThenElse(post.get))
          //update newheads 
          newheads ++= findHeads(And(bodyExpr, postExpr))
          acc :+ (call, Some(bodyExpr), Some(postExpr))
        } else {
          newheads ++= findHeads(bodyExpr)
          acc :+ (call, Some(bodyExpr), None)
        }

      } else acc
    })
    headCalls = newheads
    unrolls
  }
}