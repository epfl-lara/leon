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
    
  /**
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
        case t: Terminal => (t,Set())
        
        case And(args) => {
          val newargs = args.map((arg) => {
            val (nexp,ncjs) = transform(arg)
            And(nexp,And((ncjs ++ ncjs).toSeq))            
          })
          (And(newargs),Set())
        }
        case Or(args) => {
          val newargs = args.map((arg) => {
            val (nexp,ncjs) = transform(arg)
            And(nexp,And((ncjs ++ ncjs).toSeq))            
          })
          (Or(newargs),Set())
        }        

        case BinaryOperator(e1, e2, op) => {
          val (nexp1,ncjs1) = transform(e1)
          val (nexp2,ncjs2) = transform(e2)
          (op(nexp1,nexp2),ncjs1 ++ ncjs2)          
        }
        
        case u @ UnaryOperator(e1, op) => {
          val (nexp,ncjs) = transform(e1)
          (op(nexp),ncjs)
        }
        case n @ NAryOperator(args, op) => {
          
          var ncjs = Set[Expr]()
          var ncalls = Set[Call]()
          val newargs = args.map((arg) =>{
            val (nexp,js) = transform(arg)
            ncjs ++= js            
            nexp
          })          
          (op(newargs),ncjs)
        }
        case _ => throw IllegalStateException("Impossible event: expr did not match any case: " + e)        
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
  var fiToVarMap = Map[FunctionInvocation, (Expr,Set[Call],Set[Expr])]()  
  def FlattenFunction(inExpr: Expr): Expr = {        
    /**
     * First return value is the new expression. The second return value is the 
     * set of new calls and the third return value is the new conjuncts
     */
    def flattenFunc(e: Expr): (Expr,Set[Call],Set[Expr]) = {
      e match {        
        case fi @ FunctionInvocation(fd, args) => {
          if(fiToVarMap.contains(fi)){
            fiToVarMap(fi)
          }            
          else {                                                                     
            //now also flatten the args. The following is slightly tricky            
            var newctrs = Seq[Expr]()
            var newConjuncts = Set[Expr]()
            var newUIFs = Set[Call]()
            
            val newargs = args.map((arg) =>              
              arg match {                
                case t : Terminal => t                                     
                case _ => {                  
                  val (nexpr,nuifs,ncjs) = flattenFunc(arg)
                  
                  newConjuncts ++= ncjs
                  newUIFs ++= nuifs 
                  
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
            newUIFs += Call(freshResVar,newfi)
            
            val res = (freshResVar, newUIFs, newConjuncts)            
            fiToVarMap += (fi -> res)
            res
          }                                
        }
        case And(args) => {
          val newargs = args.map((arg) => {
            val (nexp,nuifs,ncjs) = flattenFunc(arg)
            val uifExprs = nuifs.map((uif) => {
              Equals(uif.retexpr,uif.fi)
            })
            
            And(nexp,And((ncjs ++ uifExprs).toSeq))            
          })
          (And(newargs),Set(),Set())
        }
        case Or(args) => {
          val newargs = args.map((arg) => {
            val (nexp,nuifs,ncjs) = flattenFunc(arg)
            val uifExprs = nuifs.map((uif) => {
              Equals(uif.retexpr,uif.fi)
            })
            
            And(nexp,And((ncjs ++ uifExprs).toSeq))            
          })
          (Or(newargs),Set(),Set())
        }
        case t: Terminal => (t,Set(),Set())
        case u @ UnaryOperator(e1, op) => {
          val (nexp,ncalls,ncjs) = flattenFunc(e1)
          (op(nexp),ncalls,ncjs)
        }
        case b @ BinaryOperator(e1, e2, op) => {
          val (nexp1,ncalls1,ncjs1) = flattenFunc(e1)
          val (nexp2,ncalls2,ncjs2) = flattenFunc(e2)
          (op(nexp1,nexp2),ncalls1 ++ ncalls2,ncjs1 ++ ncjs2)          
        }
        case n @ NAryOperator(args, op) => {
          
          var ncjs = Set[Expr]()
          var ncalls = Set[Call]()
          val newargs = args.map((arg) =>{
            val (nexp,cs,js) = flattenFunc(arg)
            ncjs ++= js
            ncalls ++= cs            
            nexp
          })          
          (op(newargs),ncalls,ncjs)
        }
        case _ => throw IllegalStateException("Impossible event: expr did not match any case: " + inExpr)        
      }
    }
    //reduce the language before applying flatten function
    val newe = reduceLangBlocks(inExpr)
    
    val (nexp,nuifs,ncjs) = flattenFunc(newe)
    if(!nuifs.isEmpty || !ncjs.isEmpty) {
      val uifExprs = nuifs.map((uif) => {
        Equals(uif.retexpr, uif.fi)
      })
      And(nexp, And((ncjs ++ uifExprs).toSeq))
    }
    else nexp            
  }
}
