package leon
package invariant.util

import purescala._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import Util._
import invariant.structure.FunctionUtils._

/**
 * This represents a call graph of the functions in the program
 */
class CallGraph {
  val graph = new DirectedGraph[FunDef]()

  def addFunction(fd: FunDef) = graph.addNode(fd)

  def addEdgeIfNotPresent(src: FunDef, callee: FunDef): Unit = {
    if (!graph.containsEdge(src, callee))
      graph.addEdge(src, callee)
  }

  def callees(src: FunDef): Set[FunDef] = {
    graph.getSuccessors(src)
  }

  def transitiveCallees(src: FunDef): Set[FunDef] = {
    graph.BFSReachables(src)
  }

  def isRecursive(fd: FunDef): Boolean = {
    transitivelyCalls(fd, fd)
  }

  /**
   * Checks if the src transitively calls the procedure proc
   */
  def transitivelyCalls(src: FunDef, proc: FunDef): Boolean = {
    //important: We cannot say that src calls it self even though source is reachable from itself in the callgraph
    graph.BFSReach(src, proc, excludeSrc = true)
  }

  def calls(src: FunDef, proc: FunDef): Boolean = {
    graph.containsEdge(src, proc)
  }

  /**
   * sorting functions in ascending topological order
   */
  def topologicalOrder: Seq[FunDef] = {

    def insert(index: Int, l: Seq[FunDef], fd: FunDef): Seq[FunDef] = {
      var i = 0
      var head = Seq[FunDef]()
      l.foreach((elem) => {
        if (i == index)
          head :+= fd
        head :+= elem
        i += 1
      })
      head
    }

    var funcList = Seq[FunDef]()
    graph.getNodes.toList.foreach((f) => {
      var inserted = false
      var index = 0
      for (i <- 0 to funcList.length - 1) {
        if (!inserted && this.transitivelyCalls(funcList(i), f)) {
          index = i
          inserted = true
        }
      }
      if (!inserted)
        funcList :+= f
      else funcList = insert(index, funcList, f)
    })

    funcList
  }

  override def toString: String = {
    val procs = graph.getNodes
    procs.foldLeft("")((acc, proc) => {
      acc + proc.id + " --calls--> " +
        graph.getSuccessors(proc).foldLeft("")((acc, succ) => acc + "," + succ.id) + "\n"
    })
  }
}

object CallGraphUtil {

  def constructCallGraph(prog: Program, onlyBody: Boolean = false, withTemplates: Boolean = false): CallGraph = {
//
    // println("Constructing call graph")
    val cg = new CallGraph()
    functionsWOFields(prog.definedFunctions).foreach((fd) => {
      if (fd.hasBody) {
        // println("Adding func " + fd.id.uniqueName)
        var funExpr = fd.body.get
        if (!onlyBody) {
          if (fd.hasPrecondition)
            funExpr = Tuple(Seq(funExpr, fd.precondition.get))
          if (fd.hasPostcondition)
            funExpr = Tuple(Seq(funExpr, fd.postcondition.get))
        }
        if (withTemplates && fd.hasTemplate) {
          funExpr = Tuple(Seq(funExpr, fd.getTemplate))
        }

        //introduce a new edge for every callee
        val callees = getCallees(funExpr)
        if (callees.isEmpty)
          cg.addFunction(fd)
        else
          callees.foreach(cg.addEdgeIfNotPresent(fd, _))
      }
    })
    cg
  }

  def getCallees(expr: Expr): Set[FunDef] = {
    var callees = Set[FunDef]()
    simplePostTransform((expr) => expr match {
      //note: do not consider field invocations
      case FunctionInvocation(TypedFunDef(callee, _), args)
      	if callee.isRealFunction => {
        callees += callee
        expr
      }
      case _ => expr
    })(expr)
    callees
  }
}