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
//case class CallNode(recCaller: FunDef, call: Call)

class RefinementEngine(prog: Program, ctrTracker: ConstraintTracker) {
     
  //private var currentAbs : Expr = _  
  //private var unrolledFuncs = Set[FunDef]()
  //pointers to the nodes that have function calls  
  var headCallPtrs = findAllHeads(ctrTracker)  

  private def findAllHeads(ctrTracker: ConstraintTracker) : Map[Call,CtrNode] ={  
    var heads = Map[Call,CtrNode]()
    
    ctrTracker.getFuncs.foldLeft()((acc,fd) => {
      val (btree,ptree) = ctrTracker.getVC(fd)      
      heads ++= findHeads(btree, fd) ++  findHeads(ptree, fd)      
    }  
    heads
  }  
  
  /**
   * Heads are procedure calls whose target definitions have not been unrolled
   */
  private def findHeads(ctrTree: CtrTree, caller: FunDef) : Map[Call,CtrNode] ={  
    var heads = Map[Call,CtrNode]()

    def visitor : (CtrNode => Unit) = 
      (node: CtrNode) => {
        val calls = node.uifs
        calls.foreach((call) => { heads += (call,node) })  
      }  
    TreeUtil.preorderVisitor(ctrTree,visitor)      
    heads
  }  
  

  /**
   * Returns a set of unrolled calls.
   * This procedure may refine an existing abstraction.
   * Currently, the refinement happens by unrolling.
   *  here we unroll the methods in the current abstraction by one step
   */
  def refineAbstraction(): Seq[Call] = {
            
    //unrolledFuncs ++= headFuncs.map(_.funDef)
    
    var newheads = Map[Call,CtrNode]()
    val unrolls = headCallPtrs.foldLeft(Seq[Call]())((acc, entry) => {      

      val (call, ctrnode) = entry      
      val fi = call.fi

      if (fi.funDef.body.isDefined) {

        val body = fi.funDef.getBody
        val resFresh = Variable(FreshIdentifier("result", true).setType(body.getType))
        val bexpr1 = Equals(resFresh, body)

        val prec = fi.funDef.precondition
        val bodyExpr = InvariantUtil.FlattenFunction(if (prec.isEmpty) {
          bexpr1
        } else {
          And(matchToIfThenElse(prec.get), bexpr1)
        })        

        val isRecursive = prog.isRecursive(fi.funDef)        

        if(isRecursive) {

          /** 
           * create a new verification condition for this recursive function
           **/
          val recFun = fi.funDef
          if (!constTracker.hasCtrTree(recFun)) { //check if a constraint tree does not exist for the call's target           

            //add body constraints
            ctrTracker.addBodyConstraints(recFun, bodyExpr)

            //add (negated) post condition template for the function                              
            val argmap = InvariantUtil.formalToAcutal(
              Call(resFresh, FunctionInvocation(recFun, recFun.args.map(_.toVariable))), ResultVariable())

            val postTemp = TemplateFactory.constructTemplate(argmap, recFun)
            val npostTemp = InvariantUtil.FlattenFunction(Not(postTemp))
            //print the negated post
            //println("Negated Post: "+npostTemp)
            constTracker.addPostConstraints(recFun,npostTemp)

            //Find new heads
            (btree,ptree) = constTracker.getVC(recFun)
            newheads ++= findHeads(btree) ++ findHeads(ptree)
          }
          //TODO: add the unrolled body to the caller constraints
        }
        else {

          //here inline the body && Post and add it to the tree of the rec caller          
          val calleeSummary = if (!fi.funDef.postcondition.isEmpty) {
            
                                val post = fi.funDef.postcondition
                                val argmap1 = InvariantUtil.formalToAcutal(call, ResultVariable())
                                val inlinedPost = InvariantUtil.FlattenFunction(replace(argmap1, matchToIfThenElse(post.get)))

                                val argmap2 = InvariantUtil.formalToAcutal(call, resFresh)
                                val inlinedBody = replace(argmap2, bodyExpr)
                                And(inlinedBody, inlinedPost)
                              } else {

                                val argmap2 = InvariantUtil.formalToAcutal(call, resFresh)
                                replace(argmap2, bodyExpr)
                              }          
          //println("calleeSummary: "+calleeSummary)        
          //create a constraint tree for the summary
          val summaryTree = CtrNode()
          constTracker.addConstraintRecur(calleeSummary, summaryTree)          
          TreeUtil.insertTree(ctrnode, summaryTree)

          //Find new heads
          newheads ++= findHeads(summaryTree)
        }        
        acc :+ call

      } else acc
    })
    headCallPtrs = newheads
    unrolls
  }
}