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

class RefineVC {
     
  private var reporter: Reporter = _
  private var currentAbs : Expr = _
  private var headFuncs = Set[FunctionInvocation]()
  private var unrolledFuncs = Set[FunDef]()
  
  def RefineVC(rep: Reporter, vc: Expr, fd: FunDef) ={
    reporter = rep
    currentAbs = vc    
    unrolledFuncs += fd
    headFuncs = findHeads(vc)
  }
  
  private def findHeads(abs: Expr) : Set[FunctionInvocation] ={
    //initialize head functions
    var heads = Set[FunctionInvocation]()
    simplePostTransform((e: Expr) => e match {
      case fi@FunctionInvocation(fd,args) => {
        if(!unrolledFuncs.contains(fi.funDef))
        	heads += fi 
        fi 
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
  def refineAbstraction(): Seq[(FunctionInvocation, Option[Expr], Option[Expr])] = {
    //here we unroll the methods in the current abstraction by one step
    
    //update unrolled funcs
    unrolledFuncs ++= headFuncs.map(_.funDef)
    
    var newheads = Set[FunctionInvocation]()
    val unrolls = headFuncs.foldLeft(Seq[(FunctionInvocation, Option[Expr], Option[Expr])]())((acc, fi) => {      

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
          acc :+ (fi, Some(bodyExpr), Some(postExpr))
        } else {
          newheads ++= findHeads(bodyExpr)
          acc :+ (fi, Some(bodyExpr), None)
        }

      } else acc
    })
    headFuncs = newheads
    unrolls
  }
}