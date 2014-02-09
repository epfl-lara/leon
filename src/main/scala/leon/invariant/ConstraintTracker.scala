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

class ConstraintTracker(rootFun : FunDef) {

  //verification conditions for each procedure.
  //Each verification condition is an implication where the antecedent and the consequent are represented as DNF trees.
  //The verification conditions may have templates
  private var dnfVCs = Map[FunDef,(CtrNode,CtrNode)]()  
    
  //some constants
  private val zero = IntLiteral(0)
  private val one = IntLiteral(1)
  private val mone =IntLiteral(-1)   
  private val fls = BooleanLiteral(false)
  private val tru = BooleanLiteral(true)

  def getFuncs : Seq[FunDef] = dnfVCs.keys.toSeq

  def getVC(fd: FunDef) : (CtrNode,CtrNode) = {
    dnfVCs(fd)
  }

  //adds a constraint in conjunction with  the constraint represented by parentNode
  def addConstraintRecur(inexpr: Expr, parentNode : CtrNode) : Unit = {

    //returns a node that represents the root of the constraint
    //this is passed an end node: the node that represents the last  children of the sub-tree
    def addCtr(ie: Expr, endnode: CtrNode): CtrNode = {
      ie match {
        case Or(subexprs) => {
          //create a new end node and make 'endnode' it child
          val childEndNode = CtrNode()                    
          childEndNode.addChildren(endnode)
          val children = subexprs.foldLeft(Set[CtrNode]())((acc, sube) => {                   
            acc + addCtr(sube, childEndNode)
          })
          val rootnode = CtrNode()          
          children.foreach((child) => { rootnode.addChildren(child); })                   
          rootnode
        }
        case And(subexprs) => {
          val rootnode = subexprs.foldRight(None: Option[CtrNode])((sube, acc) => {
            val currentNode = if (acc == None) addCtr(sube, endnode)
            else addCtr(sube, acc.get)
            Some(currentNode)
          })
          rootnode.get
        }        	    
        case _ => {
          val node = CtrNode()          
          ie match {
            case Variable(_) => { 
              node.boolCtrs += new BoolConstraint(ie)
            }
            case Not(Variable(_)) => {
             node.boolCtrs += new BoolConstraint(ie)            
            }
            case Equals(v@Variable(_),fi@FunctionInvocation(_,_)) => {
            	node.uifs += Call(v,fi)
            }
            //need to handle boolean calls as well
            case Iff(v@Variable(_),fi@FunctionInvocation(_,_)) => {
            	node.uifs += Call(v,fi)
            }
            case Iff(Variable(_),CaseClassInstanceOf(_,_)) | Equals(Variable(_),CaseClassSelector(_,_,_))
            	 | Iff(Variable(_),CaseClassSelector(_,_,_)) | Equals(Variable(_),CaseClass(_,_)) 
            	 | Equals(Variable(_),TupleSelect(_,_)) | Iff(Variable(_),TupleSelect(_,_)) 
            	 | Equals(Variable(_),Tuple(_)) => {

              node.adtCtrs += ADTConstraint(ie)
            }
            case Equals(lhs,rhs) if(lhs.getType != Int32Type && lhs.getType != RealType) => {
              //println("ADT constraint: "+ie)
              node.adtCtrs += ADTConstraint(ie)
            }
            case Not(Equals(lhs,rhs)) if(lhs.getType != Int32Type && lhs.getType != RealType) => {
              node.adtCtrs += ADTConstraint(ie)
            }
            case _ => {
              //val template = LinearConstraintUtil.exprToTemplate(ie)
              val template = LinearConstraintUtil.tryExprToTemplate(ie)
              if(!template.isDefined) {
                //here the expression reduced to true so drop it (note we are in nnf form)
                //TODO: can the expression reduce to false ??                
              } else{
                if(template.get.isInstanceOf[LinearConstraint])
            	  node.constraints += template.get.asInstanceOf[LinearConstraint]
                else node.templates += template.get
              }                          
            } 
          }          
          node.addChildren(endnode)
          node
        }
      }
    }
    //println("Creating constraint DAG for expresssion: "+inexpr)
    //first simplify the expression
    val simpExpr = ExpressionTransformer.simplify(simplifyArithmetic(inexpr))
    val exprRoot = addCtr(simpExpr, CtrNode())
    val parentEnd = parentNode.getEndNode
    parentEnd.addChildren(exprRoot)    
  }

  //checks if a constraint tree exists for a function 
  def hasCtrTree(fdef: FunDef) = {
  	dnfVCs.contains(fdef)
  }

	//returns the constraint tree corresponding to a function
  def getCtrTree(fdef: FunDef) : (CtrNode,CtrNode) ={
    dnfVCs.getOrElse(fdef, {
      //initialize body and post roots
      val newentry = (CtrNode(),CtrNode())
      dnfVCs += (fdef -> newentry)
      newentry
    })    
  }

  def addBodyConstraints(fdef: FunDef, body: Expr) = {
    val (bodyRoot,_) = getCtrTree(fdef)    
    addConstraintRecur(body, bodyRoot)    
  }

  /**
   * This is a little tricky the post tree contains negation of the post condition.
   * This is used for optimization.  
   */
  def addPostConstraints(fdef: FunDef, npost: Expr) = {
    val (_,postRoot) = getCtrTree(fdef)
    addConstraintRecur(npost, postRoot)   
    //println("PostCtrTree\n"+postRoot.toString)    
  }   
}