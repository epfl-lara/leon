package leon
package invariant

import purescala.DataStructures._
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
	
	/**
	 * Checks if the src transitively calls the procedure proc
	 */
	def transitivelyCalls(src: FunDef, proc: FunDef) : Boolean = {
	  graph.BFSReach(src, proc)
	}
		
	def calls(src: FunDef, proc: FunDef) : Boolean = {
	  graph.containsEdge(src, proc)
	}
}

object ProgramCallGraph {
  def getCallGraph(prog : Program) : CallGraph = {
	
    val cg = new CallGraph()
    
    prog.definedFunctions.foreach((fd) => {          
      if(fd.hasBody){
        var funExpr = fd.getBody
        if(fd.hasPrecondition) 
        	funExpr = Tuple(Seq(funExpr,fd.getPrecondition))
        if(fd.hasPostcondition) 
        	funExpr = Tuple(Seq(funExpr,fd.getPostcondition))
       	
        simplePreTransform((expr) => expr match {
          case FunctionInvocation(callee,args) => {
            //introduce a new edge
            cg.addEdgeIfNotPresent(fd, callee)
            
            expr
          } 
          case _ => expr
        })(funExpr)
      }
    })
    
    cg
  } 
}