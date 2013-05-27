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

//the caller field represents the last recursive caller that invoked this call or the main function.
case class CallNode(recCaller: FunDef, call: Call)

class RefinementEngine(prog: Program) {
     
  private var currentAbs : Expr = _
  private var headCalls = Set[CallNode]()
  //private var unrolledFuncs = Set[FunDef]()
  
  def this(vc: Expr, fd: FunDef, prog: Program) = {
    this(prog)    
    currentAbs = vc    
    //unrolledFuncs += fd
    headCalls = findHeads(vc, fd)
  }
  
  /**
   * Heads are procedure calls whose target definitions have not been unrolled
   */
  private def findHeads(abs: Expr, caller: FunDef) : Set[CallNode] ={
    //initialize head functions
    var heads = Set[CallNode]()
    simplePostTransform((e: Expr) => e match {
      case eq@Equals(rexp,fi@FunctionInvocation(fd,args)) => {
      //  if(!unrolledFuncs.contains(fi.funDef))
        heads += CallNode(caller,Call(rexp,fi))
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
  def refineAbstraction(): Seq[(Call, FunDef, Option[Expr], Option[Expr])] = {
    //here we unroll the methods in the current abstraction by one step
    
    //update unrolled funcs
    //unrolledFuncs ++= headFuncs.map(_.funDef)
    
    var newheads = Set[CallNode]()
    val unrolls = headCalls.foldLeft(Seq[(Call, FunDef, Option[Expr], Option[Expr])]())((acc, callnode) => {      
      
      val fi = callnode.call.fi
      if (fi.funDef.body.isDefined) {
        val body = fi.funDef.getBody
        val resFresh = Variable(FreshIdentifier("result", true).setType(body.getType))
        val bexpr = Equals(resFresh, body)

        //get the last recursive caller which would be fi.funDef or callnode.recCaller
        val recCaller = if(prog.isRecursive(fi.funDef)) fi.funDef else callnode.recCaller

        val prec = fi.funDef.precondition
        val bodyExpr = if (prec.isEmpty) {
          bexpr
        } else {
          And(matchToIfThenElse(prec.get), bexpr)
        }

        val (mayBody,mayPost) = if (!fi.funDef.postcondition.isEmpty) {

          val post = fi.funDef.postcondition
          val postExpr = replace(Map(ResultVariable() -> resFresh), matchToIfThenElse(post.get))
          
          //update newheads 
          newheads ++= findHeads(And(bodyExpr, postExpr),recCaller)
          (Some(bodyExpr), Some(postExpr))
          
        } else {
          
          newheads ++= findHeads(bodyExpr, recCaller)
          (Some(bodyExpr), None)
        }

        acc :+ (callnode.call, recCaller, mayBody, mayPost)

      } else acc
    })
    headCalls = newheads
    unrolls
  }
}