package leon
package invariant

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import scala.collection.mutable.{ Set => MutableSet }
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
import scala.collection.mutable.{Set => MutableSet}

case class Call(retexpr: Expr, fi: FunctionInvocation)

object InvariantUtil {
  
  val zero = IntLiteral(0)
  val one = IntLiteral(1)

  /**
  * This function conjoins the conjuncts created by 'transfomer' within the clauses containing Expr.
  * This is meant to be used by operations that may flatten subexpression using existential quantifiers.
  **/
  def conjoinWithinClause(e: Expr, transformer : Expr => (Expr,Set[Expr])) : (Expr, Set[Expr]) = 
  e match {        
      case And(args) => {
        val newargs = args.map((arg) => {

          val (nexp,ncjs) = transformer(arg)

          And(nexp,And(ncjs.toSeq))            
        })
        (And(newargs),Set())
      }
      case Or(args) => {
        val newargs = args.map((arg) => {

          val (nexp,ncjs) = transformer(arg)

          And(nexp,And(ncjs.toSeq))            
        })
        (Or(newargs),Set())
      }
      case t: Terminal => (t,Set())                
      case BinaryOperator(e1, e2, op) => {
       
        val (nexp1,ncjs1) = transformer(e1)
        val (nexp2,ncjs2) = transformer(e2)

        (op(nexp1,nexp2),ncjs1 ++ ncjs2)          
      }
      
      case u @ UnaryOperator(e1, op) => {
        
        val (nexp,ncjs) = transformer(e1)

        (op(nexp),ncjs)
      }
      case n @ NAryOperator(args, op) => {
        
        var ncjs = Set[Expr]()
        var ncalls = Set[Call]()
        val newargs = args.map((arg) =>{
        
          val (nexp,js) = transformer(arg)
          ncjs ++= js            
          nexp
        })          
        (op(newargs),ncjs)
      }
      case _ => throw IllegalStateException("Impossible event: expr did not match any case: " + e)                                
  }
    
  /**
   * Assumed that that given expression has boolean type 
   * converting if-then-else and let into a logical formula
   */
  def reduceLangBlocks(inexpr: Expr) : Expr = {
        
    def transform(e: Expr) : (Expr,Set[Expr]) = {      
      e match {        
        case Equals(lhs, rhs) => {
          rhs match {
            //this is an optimization
            case IfExpr(cond, then, elze) => {
              val newexpr = Or(And(cond, Equals(lhs, then)), And(Not(cond), Equals(lhs, elze)))
              transform(newexpr)
            }
            case _ => {
              val (nexp1, ncjs1) = transform(lhs)
              val (nexp2, ncjs2) = transform(rhs)
              (Equals(nexp1, nexp2), ncjs1 ++ ncjs2)
            }
          }
        }
        case IfExpr(cond, then, elze) => {
          val freshvar = FreshIdentifier("ifres",true).setType(e.getType).toVariable          
          val newexpr = Or(And(cond,Equals(freshvar,then)),And(Not(cond),Equals(freshvar,elze)))
          
          val resset = transform(newexpr)
          
          (freshvar, resset._2 + Equals(freshvar,resset._1)) 
        }
        case Let(binder,value,body) => {
          val freshvar = FreshIdentifier(binder.name,true).setType(e.getType).toVariable
          val newbody = replace(Map(binder.toVariable -> freshvar),body)
          
          val resbody = transform(newbody)          
          val resvalue = transform(value) 
          
          (resbody._1, resbody._2 ++ (resvalue._2 + Equals(freshvar,resvalue._1)))          
        }
        case _ =>  conjoinWithinClause(e, transform)
      }
    }
    val (nexp,ncjs) = transform(inexpr)
    if(!ncjs.isEmpty) {      
      And(nexp, And(ncjs.toSeq))
    }
    else nexp
  }

 
  /**   
   * Assumed that that given expression has boolean type   
   * (a) the function replaces every function call by a variable and creates a new equality
   * (b) it also replaces arguments that are not variables by fresh variables and creates 
   * a new equality mapping the fresh variable to the argument expression   
   */      
  //var fiToVarMap = Map[FunctionInvocation, (Expr,Set[Call],Set[Expr])]()  
  def FlattenFunction(inExpr: Expr): Expr = {        
    
    /**
     * First return value is the new expression. The second return value is the 
     * set of new conjuncts
     */
    def flattenFunc(e: Expr): (Expr,Set[Expr]) = {
      e match {
        case fi @ FunctionInvocation(fd, args) => {
          //now also flatten the args. The following is slightly tricky            
          var newctrs = Seq[Expr]()
          var newConjuncts = Set[Expr]()          
          
          val newargs = args.map((arg) =>              
            arg match {                
              case t : Terminal => t                                     
              case _ => {                  
                val (nexpr,ncjs) = flattenFunc(arg)
                
                newConjuncts ++= ncjs                
                
                nexpr match {
                  case t : Terminal => t
                  case _ => {
                  	val freshArgVar = Variable(FreshIdentifier("arg", true).setType(arg.getType))                    	                    	
                      newConjuncts += Equals(freshArgVar, nexpr) 
                      freshArgVar
                  }
                }                                    
              }
            })              
          //create a new equality in UIFs
          val newfi = FunctionInvocation(fd,newargs)
          //create a new variable to represent the function
          val freshResVar = Variable(FreshIdentifier("r", true).setType(fi.getType))
          newConjuncts += Equals(freshResVar, newfi)

          //newUIFs += Call(freshResVar,newfi)          
          val res = (freshResVar, newConjuncts)                        
          res          
        }
        case inst@CaseClassInstanceOf(cd,e1) => {
          //replace e by a variable
          val (newe,newcjs) = flattenFunc(e1)
          var newConjuncts = newcjs

          val freshArg = newe match {
            case t : Terminal => t
            case _ => {
              val freshVar = Variable(FreshIdentifier("iarg", true).setType(newe.getType))
              newConjuncts += Equals(freshVar, newe) 
              freshVar
            }
          }            
          val newInst = CaseClassInstanceOf(cd,freshArg)
          val freshResVar = Variable(FreshIdentifier("ci", true).setType(inst.getType))
          newConjuncts += Equals(freshResVar, newInst) 
          (freshResVar, newConjuncts)
        }
        case cs@CaseClassSelector(cd, e1, sel) => {
         val (newe,newcjs) = flattenFunc(e1)
          var newConjuncts = newcjs

          val freshArg = newe match {
            case t : Terminal => t
            case _ => {
              val freshVar = Variable(FreshIdentifier("inst", true).setType(newe.getType))
              newConjuncts += Equals(freshVar, newe) 
              freshVar
            }
          }            
          val newCS = CaseClassSelector(cd, freshArg, sel)
          val freshResVar = Variable(FreshIdentifier("cs", true).setType(cs.getType))
          newConjuncts += Equals(freshResVar, newCS)           
          (freshResVar, newConjuncts) 
        }
        case _ => conjoinWithinClause(e, flattenFunc)
      }
    }
    
    //convert to negated normal form         
    val nnfExpr = TransformNot(inExpr)    
    //reduce the language before applying flatten function
    val newe = TransformNot(reduceLangBlocks(nnfExpr))
    
    val (nexp,ncjs) = flattenFunc(newe)
    if(!ncjs.isEmpty) {      
      And(nexp, And(ncjs.toSeq))
    }
    else nexp           
  }
  
  
  /**
   * The following procedure converts the formula into negated normal form by pushing all not's inside.
   * It also handles disequality constraints.
   * Some important features.
   * (a) For relations with real variables, the following produces a strict inequality
   * (b) For relations with integer variables, the strict inequalities are reduced to non-strict inequalities 
   */
  def TransformNot(expr: Expr): Expr = {
    def nnf(inExpr: Expr): Expr = {
      inExpr match {
        //matches integer binary relation
        case Not(e @ BinaryOperator(e1, e2, op)) if (e1.getType == Int32Type
            || e1.getType == RealType) => {          
          e match {
            case e: Equals => Or(nnf(LessThan(e1, e2)), nnf(GreaterThan(e1, e2)))
              /*else 
            	Or(nnf(LessEquals(e1, Minus(e2, one))), nnf(GreaterEquals(e1, Plus(e2, one))))
            }*/
            case e: LessThan => GreaterEquals(nnf(e1), nnf(e2))
            case e: LessEquals => GreaterThan(nnf(e1), nnf(e2))
            case e: GreaterThan => LessEquals(nnf(e1), nnf(e2))
            case e: GreaterEquals => LessThan(nnf(e1), nnf(e2))
            case _ => throw IllegalStateException("Unknown integer predicate: " + e)
          }
        }
        //TODO: Puzzling: "Not" is not recognized as an unary operator, need to find out why
        case e @ Not(t: Terminal) => e
        case Not(And(args)) => Or(args.map(arg => nnf(Not(arg))))
        case Not(Or(args)) => And(args.map(arg => nnf(Not(arg))))
        case Not(Not(e1)) => nnf(e1)
        case Not(Implies(e1, e2)) => And(nnf(e1), nnf(Not(e2)))
        case Not(Iff(e1, e2)) => Or(nnf(Implies(e1, e2)), nnf(Implies(e2, e1)))
        case Implies(lhs,rhs) => {
          nnf(Or(Not(lhs),rhs))
        }
        case Iff(lhs,rhs) => {
          nnf(And(Implies(lhs,rhs),Implies(rhs,lhs)))
        }                

        //handle ADTs
        case ninst @ Not(CaseClassInstanceOf(cd, e)) => Not(CaseClassInstanceOf(cd,nnf(e)))

        case t: Terminal => t
        case u @ UnaryOperator(e1, op) => op(nnf(e1))
        case b @ BinaryOperator(e1, e2, op) => op(nnf(e1), nnf(e2))
        case n @ NAryOperator(args, op) => op(args.map(nnf(_)))

        case _ => throw IllegalStateException("Impossible event: expr did not match any case: " + inExpr)
      }
    }    
    val nnfvc = nnf(expr)    
    nnfvc
  }

  //compute the formal to the actual argument mapping   
  def formalToAcutal(call : Call, resvar : Expr) : Map[Expr, Expr] = {    
    val argmap: Map[Expr, Expr] = Map(resvar -> call.retexpr) ++ call.fi.funDef.args.map(_.id.toVariable).zip(call.fi.args)
    argmap
  }
  
  /**
   * Checks if the input expression has only template variables as free variables
   */
  def isTemplateExpr(expr : Expr) :Boolean ={
    var foundVar = false    
    simplePostTransform((e : Expr) => e match {    
      case Variable(id) => { 
        if(!TemplateFactory.IsTemplateIdentifier(id))
          foundVar = true
        e
      }
      case ResultVariable() => {
	     foundVar = true
	     e
      }
      case _ => e
    })(expr)
    
    !foundVar
  }
  
  def getTemplateVars(expr: Expr) : Set[Variable] = {
    var tempVars = Set[Variable]()    
    simplePostTransform((e : Expr) => e match {
      case t@Variable(id) => {
        if(TemplateFactory.IsTemplateIdentifier(id))
        	tempVars += t
        e       
      }
      case _ => e
    })(expr)
    
    tempVars
  }

  /**
   * Checks if the expression has real valued sub-expressions.
   */
  def hasReals(expr : Expr) : Boolean = {
    var foundReal = false
    simplePostTransform((e :Expr) => e match {
      case _ => { 
        if(e.getType == RealType) 
          foundReal = true;
        e      
      }    		  	
    })(expr)
    foundReal
  }
}
