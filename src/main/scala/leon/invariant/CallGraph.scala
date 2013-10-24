package leon
package invariant

import purescala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._

/**
 * This represents a call graph of the functions in the program
 */
class CallGraph {
	val graph = new DirectedGraph[FunDef]()
	
	def addEdgeIfNotPresent(src:FunDef, callee: FunDef) : Unit = {
	  if(!graph.containsEdge(src, callee))
		  graph.addEdge(src, callee)
	}
	
	def transitiveCallees(src: FunDef) : Set[FunDef] = {
	  graph.BFSReachables(src)
	}
	
	/**
	 * Checks if the src transitively calls the procedure proc
	 */
	def transitivelyCalls(src: FunDef, proc: FunDef) : Boolean = {
	  graph.BFSReach(src, proc)
	}
		
	def calls(src: FunDef, proc: FunDef) : Boolean = {
	  graph.containsEdge(src, proc)
	}
	
	override def toString : String = {
	  val procs = graph.getNodes
	  procs.foldLeft("")((acc, proc) => {
	    acc + proc.id + " --calls--> " + 
	    		graph.getSuccessors(proc).foldLeft("")((acc, succ) => acc + "," + succ.id) + "\n"	    			    
	  })
	}
}

object CallGraphUtil {
  
  def constructCallGraph(prog : Program) : CallGraph = {
	
    val cg = new CallGraph()    
    prog.definedFunctions.foreach((fd) => {          
      if(fd.hasBody){
        var funExpr = fd.body.get
        if(fd.hasPrecondition) 
        	funExpr = Tuple(Seq(funExpr,fd.precondition.get))
        if(fd.hasPostcondition) 
        	funExpr = Tuple(Seq(funExpr,fd.postcondition.get._2))
       	
        //introduce a new edge for every callee
        getCallees(funExpr).foreach(cg.addEdgeIfNotPresent(fd, _))            
      }
    })    
    cg
  }

  def getCallees(expr: Expr): Set[FunDef] = {
    var callees = Set[FunDef]()
    simplePreTransform((expr) => expr match {
      case FunctionInvocation(callee, args) => {
        callees += callee
        expr
      }
      case _ => expr
    })(expr)
    callees
  }
}