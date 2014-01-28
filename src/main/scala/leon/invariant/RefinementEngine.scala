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
import leon.purescala.ScalaPrinter

class CallData(val ctrnode : CtrNode, val parents: List[FunDef]) {  
}

//TODO: the parts of the code that collect the new head functions is ugly and has many side-effects. Fix this.
//TODO: Try targeted unrolling
class RefinementEngine(prog: Program, ctrTracker: ConstraintTracker, tempFactory : TemplateFactory, reporter : Reporter) {
    
  val tru = BooleanLiteral(true)
  //this count indicates the number of times we unroll a recursive call
  private val MAX_UNROLLS = 2
  
  //a mapping from a call to the node containing the call (plus some additional data like the list of transitive callers etc.)
  private var callDataMap = Map[Call, CallData]()
  
  //a set of calls that have not been unrolled (these are potential unroll candidates)
  //However, these calls except those given by the unspecdCalls have been specified
  private var headCalls = Set[Call]()

  //a set of functions for which we can assume templates
  private var useTemplates = Set[FunDef]()
  
  //a set of calls for which templates or specifications have not been assumed
  //TODO: Ideally these info should stored in a distributed way inside the nodes of the constraint tree
  private var untemplatedCalls = Set[Call]()  
  private var unspecdCalls = Set[Call]()

  /**
  * This creates an initial abstraction 
  **/
  def initialize() : Unit = {
    
    //we can use templates for all the functions in the ctrTracker
    useTemplates ++= ctrTracker.getFuncs
    
    //This procedure has side-effects on many fields.
    headCalls = findAllHeads(ctrTracker)
    
    //for debugging
    //println("Head-Calls: "+headCallPtrs.keys.toSeq)
    //System.exit(0)
    
    //This procedure has side-effects on many fields.   
    headCalls ++= assumeSpecifications(headCalls)
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
  def refineAbstraction(toRefineCalls : Option[Set[Call]]): Set[Call] = {
    var newheads = Set[Call]()    
    
    //unroll each call in the head pointers (and in toRefineCalls)
    val callsToProcess = if(toRefineCalls.isDefined){
      
      //pick only those calls that have been least unrolled      
      val relevCalls = headCalls.intersect(toRefineCalls.get)
      var minUnrollings = MAX_UNROLLS
      var minCalls = Set[Call]()
      relevCalls.foreach((call) => {
        val calldata = callDataMap(call)            
        val occurrences  = calldata.parents.count(_ == call.fi.funDef)
        if(occurrences < minUnrollings) {
          minUnrollings = occurrences
          minCalls = Set(call)
        }
        else if(occurrences == minUnrollings) {
          minCalls += call
        }        
      })
      //minCalls are calls that have been least unrolled
      minCalls
      
    } else headCalls
    
    println("Unrolling: "+ callsToProcess.size+"/"+headCalls.size)
    println("Unrolled calls: "+callsToProcess.map(_.expr))
    
    val unrolls = callsToProcess.foldLeft(Set[Call]())((acc, call) => {      

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
      //TODO: are there better ways of unrolling ??      
    })
    
    //update the head functions 
    headCalls = headCalls.diff(callsToProcess) ++ newheads

    if (!unrolls.isEmpty) {
      //assume the post-conditions for the calls in the VCs
      headCalls ++= assumeSpecifications(newheads)
    }    
    unrolls
  }
  
  def shouldCreateCtrTree(recFun: FunDef) : Boolean = {
    if(ctrTracker.hasCtrTree(recFun)) false
    else {
      /*val temp = tempFactory.getTemplate(recFun)
      if(!temp.isDefined) true
      else {
        if(InvariantUtil.getTemplateVars(temp.get).isEmpty) false
        else true
      }*/
      true
    }
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
        useTemplates += recFun
        
        //check if we need to create a constraint tree for the call's target
        //if (!ctrTracker.hasCtrTree(recFun) ) {                     
        if (shouldCreateCtrTree(recFun)) {
          /**
           * create a new verification condition for this recursive function
           */
          println("Creating VC for "+fi.funDef.id)
          val freshBody = freshenLocals(matchToIfThenElse(recFun.nondetBody.get))
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
    //val post = callee.postcondition
    
    //Important: make sure we use a fresh body expression here    
    val freshBody = freshenLocals(matchToIfThenElse(callee.nondetBody.get))
    val calleeSummary = 
      Equals(InvariantUtil.getFunctionReturnVariable(callee), freshBody)       
    val argmap1 = InvariantUtil.formalToAcutal(call)
    val inlinedSummary = ExpressionTransformer.normalizeExpr(replace(argmap1, calleeSummary))

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

  /**
   * This function refines the constraint tree by assuming the specifications/templates for calls in
   * the body and post tree.
   * Here, assume (pre => post ^ template)
   * Important: adding templates for unspecdCalls of the previous iterations is empirically more effective
   */
  def assumeSpecifications(newheads : Set[Call]): Set[Call] = {    
    //initialized unspecd calls
    unspecdCalls ++= newheads   
    
    var foundheads = Set[Call]()    
    //assume specifications    
    unspecdCalls.foreach((call) => {
      //first get the spec for the call if it exists 
      val spec = specForCall(call)
      if (spec.isDefined && spec.get != tru) {
        //create the root of a new  tree          
        val specTree = CtrNode()        
        ctrTracker.addConstraintRecur(spec.get, specTree)

        //find new heads            
        val cdata = callDataMap(call)
        foundheads ++= findHeads(specTree, cdata.parents)
        //insert the templateTree after this node
        TreeUtil.insertTree(cdata.ctrnode, specTree)
      }
    })

    //try to assume templates for all the current un-templated calls    
    var newUntemplatedCalls = Set[Call]()    
    untemplatedCalls.foreach((call) => {
      //first get the template for the call if one needs to be added
      if (useTemplates.contains(call.fi.funDef)) {
        val temp = templateForCall(call)
        //create the root of a new  tree          
        val tempTree = CtrNode()        
        ctrTracker.addConstraintRecur(temp, tempTree)

        //find new heads            
        val cdata = callDataMap(call)
        foundheads ++= findHeads(tempTree, cdata.parents)
        //insert the templateTree after this node
        TreeUtil.insertTree(cdata.ctrnode, tempTree)
      } else {
        newUntemplatedCalls += call
      }
    })
    untemplatedCalls = newUntemplatedCalls    
    
    //add unspecd calls to untemplatedcalls
    untemplatedCalls ++= unspecdCalls
    //update unspecd calls
    unspecdCalls = foundheads
    foundheads
  }

  def specForCall(call: Call): Option[Expr] = {
    val argmap = InvariantUtil.formalToAcutal(call)
    val callee = call.fi.funDef
    if (callee.hasPostcondition) {
      val (resvar, post) = callee.postcondition.get
      val freshPost = freshenLocals(matchToIfThenElse(post))

      val spec = if (callee.hasPrecondition) {
        val freshPre = freshenLocals(matchToIfThenElse(callee.precondition.get))
        Implies(freshPre, freshPost)
      } else {
        freshPost
      }
      val inlinedSpec = ExpressionTransformer.normalizeExpr(replace(argmap, spec))
      Some(inlinedSpec)
    } else {
      None
    }
  }

  /**
   * A helper function that creates templates for a call
   */
  def templateForCall(call: Call): Expr = {
    val argmap = InvariantUtil.formalToAcutal(call)
    val tempExpr = tempFactory.constructTemplate(argmap, call.fi.funDef)
    val template = if (call.fi.funDef.hasPrecondition) {
      val freshPre = replace(argmap, freshenLocals(matchToIfThenElse(call.fi.funDef.precondition.get)))
      Implies(freshPre, tempExpr)
    } else {
      tempExpr
    }
    //flatten functions
    //TODO: should we freshen locals here ??
    ExpressionTransformer.normalizeExpr(template)
  }
}
