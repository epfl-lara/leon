package leon
package invariant

import z3.scala._
import purescala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import solvers.{ Solver, TimeoutSolver }
import solvers.z3.FairZ3Solver
import scala.collection.mutable.{ Set => MutableSet }
import scala.collection.mutable.{ Map => MutableMap }
import scala.collection.immutable._
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
  override def prettyPrint(level : Int) : String = "Nil"
}

object GlobalNodeCounter {
	var id = 0	
	def getUID : Int = {
	  id += 1
	  id
	} 
}

case class CtrNode(id : Int = GlobalNodeCounter.getUID) extends CtrTree {

//  //constraints
//  var constraints = Set[LinearConstraint]()
//  //templates that aren't constraints
//  var templates = Set[LinearTemplate]()
//  //UI function calls
//  var uifs = Set[Call]()
//  //Abstract Data type constraints
//  var adtCtrs = Set[ADTConstraint]()
//  //Boolean Constraints
//  var boolCtrs = Set[BoolConstraint]()
  
  var uifs = Set[Call]()
  var atoms = Seq[Expr]()

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
    if (children.size == 1 && children.contains(CtrLeaf()))
      children = Set[CtrTree](child)
    else
      children += child
  }

  def getEndNode : CtrNode = {    
  	if (children.size == 1 && children.contains(CtrLeaf())) this
  	else {
  	 val n@CtrNode(_) = children.toSeq(0)
  	 n.getEndNode
  	}
  }

  override def prettyPrint(level : Int) : String = {
    var str = "Id: "+id     
    if(!atoms.isEmpty) str += " Atoms: " + atoms
    if(!uifs.isEmpty) str+= " Calls: " + uifs
//    if(!templates.isEmpty) str += " Temps: " + templates
//    if(!adtCtrs.isEmpty) str += " Adts: "+ adtCtrs
//    if(!boolCtrs.isEmpty) str += " Bools: "+boolCtrs

    str += " children: "
    children.foldLeft(str)((g: String, node: CtrTree) => { g + "\n" + " " * level +  node.prettyPrint(level + 1) })
  }
  
  def toExpr : Expr={    
    val tru = BooleanLiteral(true)
    val expr = And(atoms ++ uifs.map(_.expr).toSeq)     
    expr
  } 

  override def toString(): String = {
    prettyPrint(0)
  }   
  
  //TODO: should we dump the tree in a graph format ??
}

object TreeUtil {
  
  val tru = BooleanLiteral(true)
  
  /**
   * Creates an expression representing the tree (or DAG).
   * Here, we exploit the fact that this not any arbitrary tree but a DNF tree (or DAG) which
   * has a fork join structure of the DAG.
   */
  def toExpr(topNode: CtrTree) : Expr = {        
	//First compute join and fork points in the DAG
    var forkJoinMap = MutableMap[CtrNode,CtrTree]()             
    var visited = Set[CtrNode]()    
    //a stack that records all the join points (in topological order)    
    var joinPtsStack = Stack[CtrTree]()   
    def findForkJoinPts(root: CtrTree): Unit = root match {
      case n @ CtrNode(_) => {
        if (!visited.contains(n)) {
          visited += n

          n.Children.foreach(findForkJoinPts(_))

          if (n.Children.size > 1) {
            //this is a  fork point, make the most recent join point the join node of the fork node
            val joinNode = joinPtsStack.top
            //here we may to pop all the duplicates but the 'endnode' logic introduces some complexity.
            //to handle this we pop only #(children) - 1 elements
            for (i <- 1 to (n.Children.size - 1)) {
              //make sure that all the popped elements are the same
              if (joinNode != joinPtsStack.top)
                throw IllegalStateException("DAG not in fork-join structure: " + n)
              joinPtsStack = joinPtsStack.pop
            }
            forkJoinMap += (n -> joinNode)
          }
        } else {
          //this is a join node
          joinPtsStack = joinPtsStack.push(n)
        }
      }
      case l @ CtrLeaf() => {
        //we consider this as a join node
        joinPtsStack = joinPtsStack.push(l)
      }
    }
    
    //do a post-order visit and construct the expression
    var visited2 = Set[CtrNode]()
    //the function returns two values: a map from join points to their expression (until the next unmatched join point), 
    //an expression represented by the node until the next unmatched join point
    def computeExpr(root: CtrTree) : (Expr,Map[CtrTree,Expr]) = root match {
      case n@CtrNode(_) => {        
        if(!visited2.contains(n)) {          
          visited2 += n
          val nodeExpr = n.toExpr
          
          var joinExprMap = Map[CtrTree,Expr]()
          val chExprs = n.Children.foldLeft(Seq[Expr]())((acc, child) => { 
            val (ex, map) =  computeExpr(child)
            joinExprMap ++= map
            if(ex == tru) acc
            else (acc :+ ex)
          })
          
          //check if the 'n' is a join node
          if(forkJoinMap.exists(_._2 == n)){
            //this is a join node                       
            val joinExpr = And(nodeExpr +: chExprs)
            joinExprMap += (n -> joinExpr)
            (tru, joinExprMap)
          } 
          else if(forkJoinMap.contains(n)){
            //this is a fork node             
            val joinNode = forkJoinMap(n)
            if(!joinExprMap.contains(joinNode)) 
              throw IllegalStateException("cannot find join-expr for join node: "+joinNode+" \nTree: "+topNode)
            
            val joinExpr = joinExprMap(joinNode)             
            val forkExpr = And(Seq(nodeExpr,Or(chExprs), joinExpr))             
            (forkExpr, joinExprMap)
          } 
          else {
            (And(n.toExpr +: chExprs),joinExprMap)
          }                              
        } 
        else {
          //this is a join node (the map will actually be created the first time this node is encountered)
          (tru, Map())
        }      
      }
      case l@CtrLeaf() => {        
        //this is a join node
        (tru,Map(CtrLeaf() -> tru))
      }
    }
    
    topNode match{
      case CtrLeaf() => tru
      case _ => {
    	  findForkJoinPts(topNode)
    	  //For debugging
    	  //println("ForkJoinMap: "+forkJoinMap.map((elem) => (elem._1.id, if(elem._2 == CtrLeaf()) 0 else elem._2.asInstanceOf[CtrNode].id)))
    	  computeExpr(topNode)._1
      }
    }    
  }
  
  
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
