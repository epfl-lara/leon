package leon
package invariant

import z3.scala._
import purescala.DataStructures._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import solvers.{ Solver, TrivialSolver, TimeoutSolver }
import solvers.z3.FairZ3Solver
import scala.collection.mutable.{ Set => MutableSet }
import scala.collection.mutable.{ Map => MutableMap }
import leon.evaluators._
import java.io._
import leon.solvers.z3.UninterpretedZ3Solver
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

//A DAG that represents a DNF formula. Every path in the DAG corresponds to a disjunct
//TODO: Maintenance Issue: Fix this entire portion of code that manipulates the tree
abstract class CtrTree {
  def prettyPrint(level: Int) : String
}
case class CtrLeaf() extends CtrTree {
  override def prettyPrint(level : Int) : String = ""
}

object GlobalNodeCounter {
	var id = 0	
	def getUID : Int = {
	  id += 1
	  id
	} 
}

case class CtrNode(id : Int = GlobalNodeCounter.getUID) extends CtrTree {

	//constraints
  var constraints = Set[LinearConstraint]()
  //templates that aren't constraints
  var templates = Set[LinearTemplate]()
  //UI function calls
  var uifs = Set[Call]()
  //children in the DNF tree
  private var children = Set[CtrTree](CtrLeaf())

  def Children: Set[CtrTree] = children

  def copyChildren(newnode: CtrNode) = {
    newnode.children = this.children
  }

  def removeAllChildren() = {
    this.children = Set(CtrLeaf())
  }

  def addChildren(child: CtrNode) = {
    if (children.size == 1 && children.first == CtrLeaf())
      children = Set[CtrTree](child)
    else
      children += child
  }

  def getEndNode : CtrNode = {    
  	if(children.first == CtrLeaf()) this
  	else {
  	 val n@CtrNode(_) = children.first
  	 n.getEndNode
  	}
  }

  override def prettyPrint(level : Int) : String = {
    var str = " Ctrs: " + constraints + " Calls: " + uifs + " temps: " + templates +" children: "
    children.foldLeft(str)((g: String, node: CtrTree) => { g + "\n" + "\t" * level +  node.prettyPrint(level + 1) })
  }

  override def toString(): String = {
    prettyPrint(0)
  }
}

object TreeUtil {

  def preorderVisit(root: CtrTree, visitor: CtrNode => Unit) = {
    var visited = Set[CtrNode]()

    def preorderVisitRecur(root: CtrTree) : Unit = root match {
      case n@CtrNode(_) => {
        if(!visited.contains(n)) {

          visitor(n)
          visited += n
          n.Children.foreach(preorderVisitRecur(_))  
        }      
      }
      case CtrLeaf() => ;
    }

    preorderVisitRecur(root)
  }

  def insertTree(node: CtrNode, tree: CtrNode) : Unit = {

    val children = node.Children
    node.removeAllChildren()
    node.addChildren(tree)

    val treeEndNode = tree.getEndNode
    children.foreach((child) => {

      if(child.isInstanceOf[CtrNode])
        treeEndNode.addChildren(child.asInstanceOf[CtrNode])
    })
  }
}
