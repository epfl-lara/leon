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
                 | Equals(Variable(_),CaseClass(_,_)) | Equals(Variable(_),TupleSelect(_,_)) 
                 | Equals(Variable(_),Tuple(_)) => {

              node.adtCtrs += new ADTConstraint(ie)
            }
            case Equals(lhs,rhs) if(lhs.getType != Int32Type && lhs.getType != RealType) => {
              //println("ADT constraint: "+ie)
              node.adtCtrs += new ADTConstraint(ie)
            }
            case Not(Equals(lhs,rhs)) if(lhs.getType != Int32Type && lhs.getType != RealType) => {
              node.adtCtrs += new ADTConstraint(ie)
            }
            case _ => {
              val template = exprToTemplate(ie)
              if(template.isInstanceOf[LinearConstraint])
            	  node.constraints += template.asInstanceOf[LinearConstraint]
              else node.templates += template            
            } 
          }          
          node.addChildren(endnode)
          node
        }
      }
    }
    //println("Creating constraint DAG for expresssion: "+inexpr)
    val exprRoot = addCtr(inexpr, CtrNode())
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

  /**
   * the expression 'Expr' is required to be a linear atomic predicate (or a template),
   * if not, an exception would be thrown.
   * For now some of the constructs are not handled.
   * The function returns a linear template or a linear constraint depending
   * on whether the expression has template variables or not
   */
  def exprToTemplate(expr: Expr): LinearTemplate = {
    
    //these are the result values
    var coeffMap = MutableMap[Expr, Expr]()
    var constant: Option[Expr] = None
    var isTemplate : Boolean = false

    def addCoefficient(term: Expr, coeff: Expr) = {
      if (coeffMap.contains(term)) {
        val value = coeffMap(term)        
        coeffMap.update(term, Plus(value, coeff))
      } else coeffMap += (term -> coeff)

      if (!variablesOf(coeff).isEmpty) {
        isTemplate = true
      }
    }
    
    def addConstant(coeff: Expr) ={
      if (constant.isDefined) {
        val value = constant.get
        constant = Some(Plus(value, coeff))
      } else 
        constant = Some(coeff)

      if (!variablesOf(coeff).isEmpty) {
        isTemplate = true
      }
    }
   
    val linearExpr = MakeLinear(expr)

    //the top most operator should be a relation
    val BinaryOperator(lhs, IntLiteral(0), op) = linearExpr
    if (lhs.isInstanceOf[IntLiteral])
      throw IllegalStateException("relation on two integers, not in canonical form: " + linearExpr)

    //recurse into plus and get all minterms
    def getMinTerms(lexpr: Expr): Seq[Expr] = lexpr match {
      case Plus(e1, e2) => getMinTerms(e1) ++ getMinTerms(e2)      
      case _ => Seq(lexpr)
    }
    val minterms =  getMinTerms(lhs)

    //handle each minterm
    minterms.foreach((minterm: Expr) => minterm match {
      case _ if (InvariantUtil.isTemplateExpr(minterm)) => {
        addConstant(minterm)
      }
      case Times(e1, e2) => {
        e2 match {
          case Variable(_) => ;
          case ResultVariable() => ;
          case FunctionInvocation(_, _) => ;
          case _ => throw IllegalStateException("Multiplicand not a constraint variable: " + e2)
        }
        e1 match {
          //case c @ IntLiteral(_) => addCoefficient(e2, c)
          case _ if (InvariantUtil.isTemplateExpr(e1)) => {
            addCoefficient(e2, e1)            
          }
          case _ => throw IllegalStateException("Coefficient not a constant or template expression: " + e1)
        }
      }            
      case Variable(_) => {
        //here the coefficient is 1
        addCoefficient(minterm, one)
      }
      case ResultVariable() => {
        addCoefficient(minterm, one)
      }
      case _ => throw IllegalStateException("Unhandled min term: " + minterm)
    })

    if(isTemplate) {  
      new LinearTemplate(op, coeffMap.toMap, constant)
    }else{
      new LinearConstraint(op, coeffMap.toMap,constant)      
    }         
  }

  /**
   * This method may have to do all sorts of transformation to make the expressions linear constraints.
   * This assumes that the input expression is an atomic predicate (i.e, without and, or and nots)
   * This is subjected to constant modification.
   */
  def MakeLinear(atom: Expr): Expr = {

    //pushes the minus inside the arithmetic terms
    //we assume that inExpr is in linear form
    def PushMinus(inExpr: Expr): Expr = {
      require(inExpr.getType == Int32Type || inExpr.getType == RealType)

      inExpr match {
        case IntLiteral(v) => IntLiteral(-v)
        case t: Terminal => Times(mone, t)
        case fi @ FunctionInvocation(fdef, args) => Times(mone, fi)
        case UMinus(e1) => e1
        case Minus(e1, e2) => Plus(PushMinus(e1), e2)
        case Plus(e1, e2) => Plus(PushMinus(e1), PushMinus(e2))
        case Times(e1, e2) => {
          //here push the minus in to the coefficient which is the first argument
          Times(PushMinus(e1), e2)          
        }
        case _ => throw NotImplementedException("PushMinus -- Operators not yet handled: " + inExpr)
      }
    }

    //we assume that ine is in linear form
    def PushTimes(mul: Expr, ine: Expr): Expr = {
      ine match {
        //case IntLiteral(v) => IntLiteral(c * v)
        case t: Terminal => Times(mul, t)
        case fi @ FunctionInvocation(fdef, args) => Times(mul, fi)
        case Plus(e1, e2) => Plus(PushTimes(mul, e1), PushTimes(mul, e2))
        case Times(e1, e2) => {
          //here push the times into the coefficient which should be the first expression
          Times(PushTimes(mul, e1), e2)
        }
        case _ => throw NotImplementedException("PushTimes -- Operators not yet handled: " + ine)
      }
    }

    //collect all the constants in addition and simplify them
    //we assume that ine is in linear form
    def simplifyConsts(ine: Expr): (Option[Expr], Int) = {
      require(ine.getType == Int32Type || ine.getType == RealType)

      ine match {
        case IntLiteral(v) => (None, v)
        case Plus(e1, e2) => {
          val (r1, c1) = simplifyConsts(e1)
          val (r2, c2) = simplifyConsts(e2)

          val newe = (r1, r2) match {
            case (None, None) => None
            case (Some(t), None) => Some(t)
            case (None, Some(t)) => Some(t)
            case (Some(t1), Some(t2)) => Some(Plus(t1, t2))
          }
          (newe, c1 + c2)
        }
        case _ => (Some(ine), 0)                
      }
    }

    def mkLinearRecur(inExpr: Expr): Expr = {
      inExpr match {
        case e @ BinaryOperator(e1, e2, op) 
        if ((e.isInstanceOf[Equals] || e.isInstanceOf[LessThan]
            || e.isInstanceOf[LessEquals] || e.isInstanceOf[GreaterThan]
            || e.isInstanceOf[GreaterEquals])) => {

          //check if the expression has real valued sub-expressions
          val isReal = InvariantUtil.hasReals(e1) || InvariantUtil.hasReals(e2) 
          val (newe, newop) = e match {
            case t: Equals => (Minus(e1, e2), op)
            case t: LessEquals => (Minus(e1, e2), LessEquals)            
            case t: GreaterEquals => (Minus(e2, e1), LessEquals)
            case t: LessThan => {
              if (isReal)
                (Minus(e1, e2), LessThan)
              else
                (Plus(Minus(e1, e2), one), LessEquals)
            }
            case t: GreaterThan => {
              if(isReal)
                 (Minus(e2,e1),LessThan)
              else 
            	 (Plus(Minus(e2, e1), one), LessEquals)	
            }
          }
          val r = mkLinearRecur(newe)
          //simplify the resulting constants
          val (Some(r2), const) = simplifyConsts(r)
          val finale = if (const != 0) Plus(r2, IntLiteral(const)) else r2
          //println(r + " simplifies to "+finale)
          newop(finale, zero)
        }
        case Minus(e1, e2) => Plus(mkLinearRecur(e1), PushMinus(mkLinearRecur(e2)))
        case UMinus(e1) => PushMinus(mkLinearRecur(e1))
        case Times(e1, e2) => {
          val (r1, r2) = (mkLinearRecur(e1), mkLinearRecur(e2))
          
          if(InvariantUtil.isTemplateExpr(r1)) {
            PushTimes(r1, r2)
          } else if(InvariantUtil.isTemplateExpr(r2)){
            PushTimes(r2, r1)
          } else 
            throw IllegalStateException("Expression not linear: " + Times(r1, r2))                     
        }
        case Plus(e1, e2) => Plus(mkLinearRecur(e1), mkLinearRecur(e2))
        case t: Terminal => t
        case fi: FunctionInvocation => fi
        /*case UnaryOperator(e,op) => op(mkLinearRecur(e))
        case BinaryOperator(e1,e2,op) => op(mkLinearRecur(e1),mkLinearRecur(e2))
        case NAryOperator(args,op) => op(args.map(mkLinearRecur(_)))*/
        case _ => throw IllegalStateException("Expression not linear: " + inExpr)
      }
    }
    val rese = mkLinearRecur(atom)
    //println("Unnormalized Linearized expression: "+unnormLinear)
    rese
  }   
}