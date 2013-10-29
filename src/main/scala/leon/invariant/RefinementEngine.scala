package leon
package invariant

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import scala.collection.mutable.{ Set => MutableSet }
import scala.collection.mutable.{ Map => MutableMap }
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

class CallData(val ctrnode : CtrNode, val parents: List[FunDef]) {  
}

//TODO: the parts of the code that collect the new head functions is ugly and has many side-effects. Fix this.
class RefinementEngine(prog: Program, ctrTracker: ConstraintTracker, tempFactory : TemplateFactory, reporter : Reporter) {
    
  //this count indicates the number of times we unroll a recursive call
  private val MAX_UNROLLS = 2
  
  //a mapping from a call to the node containing the call (plus some additional data like the list of transitive callers etc.)
  private var callDataMap = Map[Call, CallData]()
  
  //a set of calls that have not been unrolled (there are potential unroll cadidates)
  private var headCalls = Set[Call]()

  //a set of calls for which its templates have been assumed
  //TODO: Ideally this info should stored in a distributed way inside the nodes of the constraint tree
  private var templatedCalls = Set[Call]()

  /**
  * This creates an initial abstraction 
  **/
  def initialize() : Unit = {
    
    //This procedure has side-effects on many fields.
    headCalls = findAllHeads(ctrTracker)
    
    //for debugging
    //println("Head-Calls: "+headCallPtrs.keys.toSeq)
    //System.exit(0)
    
    //This procedure has side-effects on many fields.
    //We are consciously ignoring the return value of the procedure
    assumePostConditions()
  }

  private def findAllHeads(ctrTracker: ConstraintTracker) : Set[Call] ={  
    var heads = Set[Call]()
    
    ctrTracker.getFuncs.foreach((fd) => {
      val (btree,ptree) = ctrTracker.getVC(fd)      
      heads ++= (findHeads(btree, List(fd)) ++ findHeads(ptree, List(fd)))
    })        
    heads    
  }

  /**
   * Heads are procedure calls whose target definitions have not been inlined.
   * The argument parents represents the functions in the chain of unrolls that resulted in the 'ctrTree'  node.
   * This procedure has side-effects on 'callDataMap'
   */
  private def findHeads(ctrTree: CtrTree, parents: List[FunDef]): Set[Call] = {
    var heads = Set[Call]()

    def visitor: (CtrNode => Unit) =
      (node: CtrNode) => {
        val calls = node.uifs
        calls.foreach((call) => {
          callDataMap += (call -> new CallData(node, parents))
          heads += call
        })
      }
    TreeUtil.preorderVisit(ctrTree, visitor)
    heads
  }    

  /**
   * This procedure refines the existing abstraction.
   * Currently, the refinement happens by unrolling the head functions.   
   */
  def refineAbstraction(): Set[Call] = {
    var newheads = Set[Call]()    
    
    //unroll each call in the head pointers        
    val unrolls = headCalls.foldLeft(Set[Call]())((acc, call) => {      

      val calldata = callDataMap(call)            
      val occurrences  = calldata.parents.count(_ == call.fi.funDef)
      //if the call is not a recursive call, unroll it unconditionally      
      if(occurrences == 0) {
        newheads ++= unrollCall(call, calldata)
        acc + call
      } else {
    	 //if the call is a recursive, unroll iff the number of times the recursive function occurs in the context is < MAX-UNROLL        
        if(occurrences < MAX_UNROLLS)
        {
          newheads ++= unrollCall(call, calldata)
          acc + call
        } else{
          //otherwise, drop the call. Here we are not unrolling the call
          acc 
        }         
      }
      //TODO: are there other ways of unrolling ??      
    })

    if (!unrolls.isEmpty) {
      //assume the post-conditions for the calls in the VCs 
      newheads ++= assumePostConditions()
    }

    //update the head functions
    headCalls = newheads 

    //For debugging: print the post and body root of all the functions
    /*ctrTracker.getFuncs.foreach((fd) => {
        val (btree,ptree) = ctrTracker.getVC(fd)
        println("Function: "+fd.id)
        println("\t Body Tree: "+btree.toString)
        println("\t Post Tree: "+ptree.toString)
      })*/

    unrolls
  }
  

  /**
   * Returns a set of unrolled calls and a set of new head functions   
   * here we unroll the methods in the current abstraction by one step.
   * This procedure has side-effects on 'headCalls' and 'callDataMap'
   */  
  //private var unrollCounts = MutableMap[Call,Int]()
  def unrollCall(call : Call, calldata : CallData): Set[Call] = {                

    //println("Processing: "+call)
    val fi = call.fi
    if (fi.funDef.hasBody) {

      //freshen the body and the post           
      val isRecursive = prog.isRecursive(fi.funDef)        
      if(isRecursive) {                        
        var newheads = Set[Call]()
        val recFun = fi.funDef
        //check if a constraint tree does not exist for the call's target
        if (!ctrTracker.hasCtrTree(recFun)) { 

          println("Creating VC for "+fi.funDef.id)          
          /**
           * create a new verification condition for this recursive function
           */          
          val freshBody = matchToIfThenElse(freshenLocals(recFun.body.get))
          val resvar = if (recFun.hasPostcondition) {
            //create a new result variable here for the same reason as freshening the locals,
            //which is to avoid variable capturing during unrolling            
            val origRes = recFun.postcondition.get._1
            Variable(FreshIdentifier(origRes.name, true).setType(origRes.getType))            
          } else {
            //create a new resvar
            Variable(FreshIdentifier("res", true).setType(recFun.returnType))
          }          
          val plainBody = Equals(resvar,freshBody)
          val bodyExpr = ExpressionTransformer.normalizeExpr(if (recFun.hasPrecondition) {
            And(matchToIfThenElse(recFun.precondition.get), plainBody)
          } else plainBody)
          
          //add body constraints
          ctrTracker.addBodyConstraints(recFun, bodyExpr)

          //add (negated) post condition template for the function                              
          val argmap = InvariantUtil.formalToAcutal(Call(resvar, FunctionInvocation(recFun, recFun.args.map(_.toVariable))))

          val postTemp = tempFactory.constructTemplate(argmap, recFun)
          val npostTemp = ExpressionTransformer.normalizeExpr(Not(postTemp))
          //print the negated post
          //println("Negated Post: "+npostTemp)
          ctrTracker.addPostConstraints(recFun,npostTemp)

          //Find new heads
          val (btree,ptree) = ctrTracker.getVC(recFun)
          newheads ++= (findHeads(btree, List(recFun)) ++ findHeads(ptree, List(recFun)))          
        }        
                   
        //Here, unroll the call into the caller tree
        println("Unrolling " + Equals(call.retexpr,call.fi))
        newheads ++= inilineCall(call, calldata.ctrnode, calldata.parents)          
        newheads
      }
      else {        
        //here we are unrolling a non-recursive function
        println("Inlining "+Equals(call.retexpr,call.fi))               
        inilineCall(call, calldata.ctrnode, calldata.parents)        
      }                
    } else Set()    
  }

  /**
  * The parameter 'resVar' is the result variable of the body
  **/
  def inilineCall(call : Call, ctrnode: CtrNode, parents : List[FunDef]) : Set[Call] = {    
    //here inline the body && Post and add it to the tree of the rec caller
    val callee = call.fi.funDef
    val post = callee.postcondition
    
    //Important: make sure we use a fresh body expression here
    val freshBody = matchToIfThenElse(freshenLocals(callee.body.get))    
    val calleeSummary = if (post.isDefined) {
      val (resvar, poste) = post.get
      val freshPost = matchToIfThenElse(freshenLocals(poste))
      val bodyRel = Equals(resvar.toVariable, freshBody)
      And(bodyRel, freshPost)
   } else {
      Equals(ResultVariable().setType(callee.returnType), freshBody)
    }

    val argmap1 = InvariantUtil.formalToAcutal(call)
    val inlinedSummary = ExpressionTransformer.normalizeExpr(replace(argmap1, calleeSummary))
          
    //println("calleeSummary: "+inlinedSummary)        
    //create a constraint tree for the summary
    val summaryTree = CtrNode()      
    ctrTracker.addConstraintRecur(inlinedSummary, summaryTree)          

    //Find new heads (note: should not insert summaryTree and then call findheads)
    //note: For memory efficiency, the callee is prepended to parents and not appended
    val newheads = findHeads(summaryTree, (callee +: parents))

    //insert the tree
    TreeUtil.insertTree(ctrnode, summaryTree)        

    newheads
  }

 /*
  * This function refines the constraint tree by assuming the post conditions/templates for calls in
  * the body and post tree.
  */
  def assumePostConditions() : Set[Call] = {
    
    ctrTracker.getFuncs.foldLeft(Set[Call]())((acc, fd) => {

      val (btree,ptree) = ctrTracker.getVC(fd)      
      val hds = assumePostConditionsForTree(btree, ptree, fd)            
      (acc ++ hds)
    })
  }
  
  def assumePostConditionsForTree(bodyRoot: CtrNode, postRoot : CtrNode, fd: FunDef) : Set[Call] = {
    
    /**
     * A helper function that creates templates for a call
     */
    var templateMap = Map[Call, Expr]()
    def templateForCall(call: Call): Expr = {

      templateMap.getOrElse(call, {
        val argmap = InvariantUtil.formalToAcutal(call)
        val tempExpr = tempFactory.constructTemplate(argmap, call.fi.funDef)
        templateMap += (call -> tempExpr)
        tempExpr
      })
    }

    var visited = Set[CtrNode]()
    var newheads = Set[Call]()

    //this does a post order traversal
    def assumeTemplates(root: CtrTree) : Unit = root match {

      case n @ CtrNode(_) => {

        if(!visited.contains(n)){
          visited += n

          //first recurse into the children  
          n.Children.foreach(assumeTemplates(_))

          //For debugging      
          /*if (fd.id.name.equals("size")) {
            println("Node UIFs: " + n.uifs)            
          }*/

          //now process this node
          val newCalls = n.uifs.toSeq.filter((call) => {                       
            val accept = !templatedCalls.contains(call) && ctrTracker.hasCtrTree(call.fi.funDef)
            /*if(call.fi.funDef.id.name == "size" && call.retexpr.asInstanceOf[Variable].id.name == "r14"){
              println("******** Filter value for: "+call.expr+" is "+accept)
            }*/
            accept
          })          
          
          //println("New calls: "+processedCalls)
          //update processed calls
          templatedCalls ++= newCalls 

          val templates = newCalls.map(call => {
            
            val template = templateForCall(call)          
            //flatten functions
            //TODO: should we freshen locals here ??
            val flatExpr = ExpressionTransformer.normalizeExpr(template)
            //create the root of a new  tree          
            val templateTree = CtrNode()          
            ctrTracker.addConstraintRecur(flatExpr, templateTree)

            //find new heads            
            newheads ++= findHeads(templateTree, callDataMap(call).parents)

            //insert the templateTree after this node
            TreeUtil.insertTree(n,templateTree)                                 
          })

        }                
      }      
      case CtrLeaf() => ;
    }

    /*if (fd.id.name.equals("size")) {
      println("Templated calls: "+templatedCalls)
    }*/
    assumeTemplates(bodyRoot) 
    assumeTemplates(postRoot)

    newheads
  }
}
