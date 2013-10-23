package leon
package invariant

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import scala.collection.mutable.{ Set => MutableSet }
import scala.collection.immutable.Stack
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
import java.io._

/**
 * A collection of transformation on expressions and some utility methods.
 * These operations are mostly semantic preserving (specific assumptions/requirements are specified on the operations)
 */
object ExpressionTransformer {
  
  val zero = IntLiteral(0)
  val one = IntLiteral(1)
  val tru = BooleanLiteral(true)

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
            case IfExpr(cond, thn, elze) => {
              val newexpr = Or(And(cond, Equals(lhs, thn)), And(Not(cond), Equals(lhs, elze)))
              transform(newexpr)
            }
            case _ => {
              val (nexp1, ncjs1) = transform(lhs)
              val (nexp2, ncjs2) = transform(rhs)
              (Equals(nexp1, nexp2), ncjs1 ++ ncjs2)
            }
          }
        }
        case IfExpr(cond, thn, elze) => {
          val freshvar = FreshIdentifier("ifres",true).setType(e.getType).toVariable          
          val newexpr = Or(And(cond,Equals(freshvar,thn)),And(Not(cond),Equals(freshvar,elze)))
          
          val resset = transform(newexpr)
          
          (freshvar, resset._2 + resset._1) 
        }
        case Let(binder,value,body) => {
          //TODO: do we have to consider reuse of let variables ?
          /*val freshvar = FreshIdentifier(binder.name,true).setType(value.getType).toVariable
          val newbody = replace(Map(binder.toVariable -> freshvar),body)*/
          
          val (resbody, bodycjs) = transform(body)          
          val (resvalue, valuecjs) = transform(value) 
          
          (resbody, (valuecjs + Equals(binder.toVariable,resvalue)) ++ bodycjs)          
        }
        //the value is a tuple in the following case
        case LetTuple(binders,value,body) => {
                    
          //TODO: do we have to consider reuse of let variables ?
          /*val bindvarMap : Map[Expr,Expr] = binders.map((binder) => {
            val bindvar = FreshIdentifier(binder.name,true).setType(value.getType).toVariable
            (binder.toVariable -> bindvar)            
          }).toMap
          val newbody = replace(bindvarMap,body)*/
          
          val (resbody, bodycjs) = transform(body)          
          val (resvalue, valuecjs) = transform(value)

          //here we optimize the case where resvalue itself has tuples
          val newConjuncts = resvalue match {
            case Tuple(args) => {
              binders.zip(args).map((elem) => {
                val (bind, arg) = elem
                Equals(bind.toVariable, arg)
              })
            }
            case _ => {
              //may it is better to assign resvalue to a temporary variable (if it is not already a variable)
              val (resvalue2, cjs) = resvalue match {
                case t: Terminal => (t, Seq())
                case _ => {
                  val freshres = FreshIdentifier("tres", true).setType(resvalue.getType).toVariable
                  (freshres, Seq(Equals(freshres, resvalue)))
                }
              }
              var i = 0
              val cjs2 = binders.map((bind) => {
                i += 1
                Equals(bind.toVariable, TupleSelect(resvalue2, i))
              })
              (cjs ++ cjs2)
            }
          }          
           
          (resbody, (valuecjs ++ newConjuncts) ++ bodycjs)          
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
   * Requires: The expression has to be in NNF form and without if-then-else and let constructs
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
          val (newargs, newConjuncts) = flattenArgs(args)                        
          //create a new equality in UIFs
          val newfi = FunctionInvocation(fd,newargs)
          //create a new variable to represent the function
          val freshResVar = Variable(FreshIdentifier("r", true).setType(fi.getType))                    
          val res = (freshResVar, newConjuncts + Equals(freshResVar, newfi))                        
          res          
        }
        case inst@CaseClassInstanceOf(cd,e1) => {          
          //replace e by a variable
          val (newargs,newcjs) = flattenArgs(Seq(e1))
          var newConjuncts = newcjs

          val freshArg = newargs(0)            
          val newInst = CaseClassInstanceOf(cd,freshArg)
          val freshResVar = Variable(FreshIdentifier("ci", true).setType(inst.getType))
          newConjuncts += Iff(freshResVar, newInst) 
          (freshResVar, newConjuncts)
        }
        case cs@CaseClassSelector(cd, e1, sel) => {
         val (newargs,newcjs) = flattenArgs(Seq(e1))
          var newConjuncts = newcjs

          val freshArg = newargs(0)
          val newCS = CaseClassSelector(cd, freshArg, sel)
          val freshResVar = Variable(FreshIdentifier("cs", true).setType(cs.getType))
          newConjuncts += Equals(freshResVar, newCS)           

          (freshResVar, newConjuncts) 
        }
        case ts@TupleSelect(e1,index) => {
         val (newargs,newcjs) = flattenArgs(Seq(e1))
          var newConjuncts = newcjs

          val freshArg = newargs(0)
          val newTS = TupleSelect(freshArg, index)
          val freshResVar = Variable(FreshIdentifier("ts", true).setType(ts.getType))
          newConjuncts += Equals(freshResVar, newTS)           

          (freshResVar, newConjuncts) 
        }
        case cc@CaseClass(cd, args) => {

          val (newargs,newcjs) = flattenArgs(args)
          var newConjuncts = newcjs

          val newCC = CaseClass(cd, newargs)
          val freshResVar = Variable(FreshIdentifier("cc", true).setType(cc.getType))
          newConjuncts += Equals(freshResVar, newCC)

          (freshResVar, newConjuncts)  
        }
        case tp@Tuple(args) => {
          val (newargs,newcjs) = flattenArgs(args)
          var newConjuncts = newcjs

          val newTP = Tuple(newargs)
          val freshResVar = Variable(FreshIdentifier("tp", true).setType(tp.getType))
          newConjuncts += Equals(freshResVar, newTP)

          (freshResVar, newConjuncts)  
        }
        case _ => conjoinWithinClause(e, flattenFunc)
      }
    }

    def flattenArgs(args : Seq[Expr]): (Seq[Expr],Set[Expr]) = {
      var newConjuncts = Set[Expr]()                  
      val newargs = args.map((arg) =>              
        arg match {                
          case v : Variable => v
          case r : ResultVariable => r
          case _ => {                  
            val (nexpr,ncjs) = flattenFunc(arg)
            
            newConjuncts ++= ncjs                
            
            nexpr match {
              case v : Variable => v
              case r : ResultVariable => r
              case _ => {
                val freshArgVar = Variable(FreshIdentifier("arg", true).setType(arg.getType))                                           
                  newConjuncts += Equals(freshArgVar, nexpr) 
                  freshArgVar
              }
            }                                    
          }
      })
      (newargs, newConjuncts)
    }
    
/*    //convert to negated normal form         
    val nnfExpr = TransformNot(inExpr)    
    //reduce the language before applying flatten function
    val newe = TransformNot(reduceLangBlocks(nnfExpr))  
*/    
    val (nexp,ncjs) = flattenFunc(inExpr)
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
        case Not(e @ BinaryOperator(e1, e2, op)) => {
          if (e1.getType == Int32Type || e1.getType == RealType) {          
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
          else{
            //in this case e1 and e2 could represent ADTs
            e match {
              case e: Equals => inExpr
              case _ => throw IllegalStateException("Unknown operation on algebraic data types: " + e)
            } 
          }
        }
        //TODO: Puzzling: "Not" is not recognized as an unary operator, need to find out why
        case e @ Not(t: Terminal) => e
        case e @ Not(FunctionInvocation(_,_)) => e 
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
  
  /**
   * Eliminates redundant nesting of ORs and ANDs.
   * This is supposed to be a semantic preserving transformation
   */
  def pullAndOrs(expr: Expr) : Expr = {
    
    simplePostTransform((e : Expr) => e match {
      case Or(args) => {
        val newArgs = args.foldLeft(Seq[Expr]())((acc, arg) => arg match {
          case Or(inArgs) => acc ++ inArgs
          case _ => acc :+ arg
        })
        Or(newArgs)
      }
      case And(args) => {
        val newArgs = args.foldLeft(Seq[Expr]())((acc, arg) => arg match {
          case And(inArgs) => acc ++ inArgs
          case _ => acc :+ arg
        })
        And(newArgs)
      }
      case _ => e
    })(expr)
  }
  
  /**
   * Normalizes the expressions
   */
  def normalizeExpr(expr: Expr) : Expr = {
    
    //convert to negated normal form         
    //val nnfExpr = TransformNot(expr)    
    //reduce the language before applying flatten function
    val redExpr = TransformNot(reduceLangBlocks(expr))
    //flatten all function calls
    val flatExpr = FlattenFunction(redExpr)
    
    //perform additional simplification
    val simpExpr = pullAndOrs(flatExpr)
    simpExpr
  }

  /**
   * This is the inverse operation of flattening, this is mostly
   * used to produce a readable formula.
   * Freevars is a set of identifiers that are program variables
   * This assumes that temporary identifiers (which are not freevars) are not reused across clauses.
   */
  def unFlatten(ine: Expr, freevars: Set[Identifier]): Expr = {
    var tempMap = Map[Expr, Expr]()
    val newinst = simplePostTransform((e: Expr) => e match {
      case Equals(v @ Variable(id), rhs @ _) if !freevars.contains(id) =>
        tempMap += (v -> rhs); tru
      case _ => e
    })(ine)
    val closure = (e: Expr) => replace(tempMap, e)
    InvariantUtil.fix(closure)(newinst)
  }
 
/*  def applyOnePointRule(param : (Expr, Stack[(Expr,Expr)], Set[Variable])) 
  	: (Expr, Stack[(Expr,Expr)],  Set[Variable]) ={ 
        
    def recReplace(expr : Expr, eqStack : Stack[(Expr,Expr)], elimVars : Set[Variable]) 
    : (Expr, Stack[(Expr,Expr)], Set[Variable]) = expr match {
      
      case v : Variable => {
        if(elimVars.contains(v)) (eqStack.toMap.apply(v), eqStack, elimVars)        	                 
        else (v, eqStack, elimVars)
      }
      case Equals(lhs, rhs) => {
        
        //replace in LHS and RHS
        val newLHS = replace(eqStack.toMap, lhs)
        val newRHS = replace(eqStack.toMap, rhs)
        val newEq = Equals(newLHS,newRHS)
        
        lhs match {
          case v : Variable => {
            if(!elimVars.contains(v)) {
              //println("Adding mapping "+v+" --> "+newRHS)
              (tru, eqStack.push((v,newRHS)), elimVars + v)
            }
            else (newEq, eqStack, elimVars)
          }
          case _ => {
            rhs match {
              case v: Variable => if (!elimVars.contains(v)) 
            	  					(tru, eqStack.push((v, newLHS)), elimVars + v)
            	  				  else (newEq, eqStack, elimVars)
              case _ => (newEq, eqStack, elimVars)
            }
          }
        }        
      }
      case And(args) =>{        
        val res = args.foldLeft((Seq[Expr](),eqStack,elimVars))((acc, e) => {
          val (currArgs, s, l)  = acc
          val (ne,ns,nl) = recReplace(e, s, l)
          (currArgs :+ ne, ns, nl)
        })
        (And(res._1), res._2, res._3)        
      }      
      case Or(args) =>{
        val newop = Or(args.map((e) => {
          
          //repeat this until a fix point
          val (ne0,s0,l0) = recReplace(e, eqStack, elimVars)
          //repeat this again
          val (ne,s,l) = recReplace(ne0, s0, l0)
          
          //add all equalities collected in this branch here.
          val eqs = s.collect{
            case elem : (Expr,Expr) if(!eqStack.contains(elem)) => Equals(elem._1,elem._2)  
          }
          if(!eqs.isEmpty)
        	  And(eqs :+ ne)
          else ne
        }))
        (newop, eqStack,elimVars)        
      }
      case t: Terminal => (t, eqStack, elimVars)
      case _ => {
        val ne = replace(eqStack.toMap, expr)
        (ne, eqStack, elimVars)
      }        
    }    
    
    val (ine, inStk, inVars) = param
    //replace the keys with values
    recReplace(ine, inStk, inVars)    
  }
  
*/  
  /*def simplifyArithWithReals(expr: Expr): Expr = {
    def simplify0(expr: Expr): Expr = expr match {
      case Plus(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 + i2)
      //case Plus(RealLiteral(n1,d1), RealLiteral(n2,d2)) => IntLiteral(i1 + i2)
      case Plus(WholeNumber(0), e) => e
      case Plus(e, WholeNumber(0)) => e
      case Plus(e1, UMinus(e2)) => Minus(e1, e2)
      case Plus(Plus(e, IntLiteral(i1)), IntLiteral(i2)) => Plus(e, IntLiteral(i1+i2))
      case Plus(Plus(IntLiteral(i1), e), IntLiteral(i2)) => Plus(IntLiteral(i1+i2), e)

      case Minus(e, WholeNumber(0)) => e
      case Minus(WholeNumber(0), e) => UMinus(e)
      case Minus(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 - i2)
      case Minus(e1, UMinus(e2)) => Plus(e1, e2)
      case Minus(e1, Minus(UMinus(e2), e3)) => Plus(e1, Plus(e2, e3))

      case UMinus(IntLiteral(x)) => IntLiteral(-x)
      case UMinus(UMinus(x)) => x
      case UMinus(Plus(UMinus(e1), e2)) => Plus(e1, UMinus(e2))
      case UMinus(Minus(e1, e2)) => Minus(e2, e1)

      case Times(WholeNumber(1), e) => e
      case Times(WholeNumber(-1), e) => UMinus(e)
      case Times(e, WholeNumber(1)) => e
      case Times(WholeNumber(0), _) => IntLiteral(0)
      case Times(_, WholeNumber(0)) => IntLiteral(0)
      case Times(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 * i2)      
      case Times(IntLiteral(i1), Times(IntLiteral(i2), t)) => Times(IntLiteral(i1*i2), t)
      case Times(IntLiteral(i1), Times(t, IntLiteral(i2))) => Times(IntLiteral(i1*i2), t)
      case Times(IntLiteral(i), UMinus(e)) => Times(IntLiteral(-i), e)
      case Times(UMinus(e), IntLiteral(i)) => Times(e, IntLiteral(-i))
      case Times(IntLiteral(i1), Division(e, IntLiteral(i2))) if i2 != 0 && i1 % i2 == 0 => Times(IntLiteral(i1/i2), e)

      case Division(IntLiteral(i1), IntLiteral(i2)) if i2 != 0 => IntLiteral(i1 / i2)
      case Division(e, IntLiteral(1)) => e

      //here we put more expensive rules
      //btw, I know those are not the most general rules, but they lead to good optimizations :)
      case Plus(UMinus(Plus(e1, e2)), e3) if e1 == e3 => UMinus(e2)
      case Plus(UMinus(Plus(e1, e2)), e3) if e2 == e3 => UMinus(e1)
      case Minus(e1, e2) if e1 == e2 => IntLiteral(0) 
      case Minus(Plus(e1, e2), Plus(e3, e4)) if e1 == e4 && e2 == e3 => IntLiteral(0)
      case Minus(Plus(e1, e2), Plus(Plus(e3, e4), e5)) if e1 == e4 && e2 == e3 => UMinus(e5)

      //default
      case e => e
    }
          

    val res = fix(simplePostTransform(simplify0))(expr)
    res
  }
  */
  
  def PrintWithIndentation(wr : PrintWriter, expr: Expr) : Unit = {
        
    def uniOP(e : Expr, seen : Int) : Boolean = e match {
      case And(args) => {
        //have we seen an or ?
        if(seen == 2)  false
        else args.foldLeft(true)((acc, arg)=> acc && uniOP(arg,1))          
      }
      case Or(args) => {
        //have we seen an And ?
        if(seen == 1)  false
        else args.foldLeft(true)((acc, arg)=> acc && uniOP(arg,2))          
      }
      case t: Terminal => true
      case u @ UnaryOperator(e1, op) => uniOP(e1,seen)
      case b @ BinaryOperator(e1, e2, op) => uniOP(e1,seen) && uniOP(e2,seen) 
      case n @ NAryOperator(args, op) => args.foldLeft(true)((acc, arg)=> acc && uniOP(arg,seen))
    }
    
    def printRec(e: Expr, indent : Int) : Unit  = {
      if(uniOP(e,0)) wr.println(e)
      else {
        wr.write("\n"+" " * indent + "(\n")
        e match {
          case And(args) => {
            var start = true
            args.map((arg) => {
              wr.print(" "*(indent+1))
              if(!start) wr.print("^")
              printRec(arg, indent + 1)
              start = false
            })
          }
          case Or(args) => {
            var start = true
            args.map((arg) => {
              wr.print(" "*(indent+1))
              if(!start) wr.print("v")
              printRec(arg, indent + 1)
              start = false
            })
          }
          case _ => throw IllegalStateException("how can this happen ? ")          
        }
        wr.write(" " * indent + ")\n")
      }      
    }    
    printRec(expr,0)
  }
}