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

	//constraints
  var constraints = Set[LinearConstraint]()
  //templates that aren't constraints
  var templates = Set[LinearTemplate]()
  //UI function calls
  var uifs = Set[Call]()
  //Abstract Data type constraints
  var adtCtrs = Set[ADTConstraint]()
  //Boolean Constraints
  var boolCtrs = Set[BoolConstraint]()

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
    var str = ""
    if(!constraints.isEmpty) str += " Ctrs: " + constraints
    if(!uifs.isEmpty) str+= " Calls: " + uifs
    if(!templates.isEmpty) str += " Temps: " + templates
    if(!adtCtrs.isEmpty) str += " Adts: "+ adtCtrs
    if(!boolCtrs.isEmpty) str += " Bools: "+boolCtrs

    str += " children: "
    children.foldLeft(str)((g: String, node: CtrTree) => { g + "\n" + " " * level +  node.prettyPrint(level + 1) })
  }
  
  def toExpr : Expr={    
    val tru = BooleanLiteral(true)
    val expr = constraints.foldLeft(tru : Expr)((acc, ctr) => if(acc == tru) ctr.expr else And(acc,ctr.expr))
    val expr2 = templates.foldLeft(expr)((acc, temp) => if(acc == tru) temp.template else And(acc,temp.template))
    val expr3 = uifs.foldLeft(expr2)((acc, call) =>if(acc == tru) call.expr  else And(acc,call.expr))
    val expr4 = adtCtrs.foldLeft(expr3)((acc, adtCtr) =>if(acc == tru) adtCtr.expr  else And(acc,adtCtr.expr))
    val expr5 = boolCtrs.foldLeft(expr4)((acc, boolCtr) =>if(acc == tru) boolCtr.expr  else And(acc,boolCtr.expr))  
    expr5
  } 

  override def toString(): String = {
    prettyPrint(0)
  }
}

object TreeUtil {
  
  val tru = BooleanLiteral(true)
  
  /**
   * Creates an expression representing the tree (or DAG).
   * Here, we exploit the fact that this not any arbitrary tree but a DNF tree (or DAG) which
   * has a fork join structure of the DAG.
   */
  def toExpr(root: CtrTree) : Expr = {        
	//First compute join and fork points in the DAG
    var forkJoinMap = MutableMap[CtrNode,CtrTree]()       
    
    //Doing a pre-order visit   
    var visited = Set[CtrNode]()
    //a stack may not be necessary, forkPts : Stack[CtrNode]
    def findForkJoinPts(root: CtrTree, forkPt : CtrNode) : Unit = root match {
      case n@CtrNode(_) => {        
        if(!visited.contains(n)) {          
          visited += n
          val fkpt = if(n.Children.size > 1) {
            
            //initalize the join point as leaf, this will be updated later when a real fork point is encountered
            forkJoinMap += (n -> CtrLeaf())
            //forkPts.push(n)
            n            
          }  else forkPt
          
          n.Children.foreach(findForkJoinPts(_, fkpt))            
        } 
        else {
          //this is the join point of the fork point at the top of 'forkPts' stack
          /*val currFork = forkPts.top
          val fkpts = forkPts.pop*/
          forkJoinMap.update(forkPt,n)          
        }      
      }
      case l@CtrLeaf() => ;
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
            val joinExpr = joinExprMap(forkJoinMap(n)) //we are bound to find the key  here            
            val forkExpr = And(Seq(nodeExpr,Or(chExprs), joinExpr))             
            (forkExpr, joinExprMap)
          } 
          else {
            (And(n.toExpr +: chExprs),joinExprMap)
          }                              
        } 
        else {
          (n.toExpr, Map())          
        }      
      }
      case l@CtrLeaf() => (tru,Map(CtrLeaf() -> tru))
    }
    
    root match{
      case CtrLeaf() => tru
      case _ => {
    	  findForkJoinPts(root, root.asInstanceOf[CtrNode])
    	  computeExpr(root)._1
      }
    }    
  }
  
  //This takes exponential time !!
/*  def toExpr(root: CtrTree) : Expr = root match {        
	case n@CtrNode(_) => {	 	  
       val childrenExpr = n.Children.foldLeft(tru: Expr)((acc, child) => {
         val chExpr = toExpr(child)
         chExpr match{
           case BooleanLiteral(tru) => acc
           case _ => if(acc == tru) chExpr else Or(acc, chExpr)
         }
       })
       val nodeExpr = n.toExpr
       
       //println("NOde: "+n.id+" Children expr: "+childrenExpr)
       if(childrenExpr== tru) nodeExpr
       else if(nodeExpr == tru) childrenExpr
       else And(nodeExpr,childrenExpr)          
	}   
    case CtrLeaf() => tru
  }*/

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
