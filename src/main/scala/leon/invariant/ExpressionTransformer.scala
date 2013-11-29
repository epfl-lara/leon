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
import scala.collection.mutable.{Map => MutableMap}
import java.io._

/**
 * A collection of transformation on expressions and some utility methods.
 * These operations are mostly semantic preserving (specific assumptions/requirements are specified on the operations)
 */
object ExpressionTransformer {
  
  val zero = IntLiteral(0)
  val one = IntLiteral(1)
  val mone = IntLiteral(-1)
  val tru = BooleanLiteral(true)    
  val fls = BooleanLiteral(false)    

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
          val freshvar = TVarFactory.createTemp("ifres").setType(e.getType).toVariable          
          val newexpr = Or(And(cond,Equals(freshvar,thn)),And(Not(cond),Equals(freshvar,elze)))
          
          val resset = transform(newexpr)
          
          (freshvar, resset._2 + resset._1) 
        }
        case Let(binder,value,body) => {
          //TODO: do we have to consider reuse of let variables ?
          /*val freshvar = TempIdFactory.createTemp(binder.name,true).setType(value.getType).toVariable
          val newbody = replace(Map(binder.toVariable -> freshvar),body)*/
          
          val (resbody, bodycjs) = transform(body)          
          val (resvalue, valuecjs) = transform(value) 
          
          (resbody, (valuecjs + Equals(binder.toVariable,resvalue)) ++ bodycjs)          
        }
        //the value is a tuple in the following case
        case LetTuple(binders,value,body) => {
                    
          //TODO: do we have to consider reuse of let variables ?
          /*val bindvarMap : Map[Expr,Expr] = binders.map((binder) => {
            val bindvar = TempIdFactory.createTemp(binder.name,true).setType(value.getType).toVariable
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
                  val freshres = TVarFactory.createTemp("tres").setType(resvalue.getType).toVariable
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
          val freshResVar = Variable(TVarFactory.createTemp("r").setType(fi.getType))                    
          val res = (freshResVar, newConjuncts + Equals(freshResVar, newfi))                        
          res          
        }
        case inst@CaseClassInstanceOf(cd,e1) => {          
          //replace e by a variable
          val (newargs,newcjs) = flattenArgs(Seq(e1))
          var newConjuncts = newcjs

          val freshArg = newargs(0)            
          val newInst = CaseClassInstanceOf(cd,freshArg)
          val freshResVar = Variable(TVarFactory.createTemp("ci").setType(inst.getType))
          newConjuncts += Iff(freshResVar, newInst) 
          (freshResVar, newConjuncts)
        }
        case cs@CaseClassSelector(cd, e1, sel) => {
         val (newargs,newcjs) = flattenArgs(Seq(e1))
          var newConjuncts = newcjs

          val freshArg = newargs(0)
          val newCS = CaseClassSelector(cd, freshArg, sel)
          val freshResVar = Variable(TVarFactory.createTemp("cs").setType(cs.getType))
          newConjuncts += Equals(freshResVar, newCS)           

          (freshResVar, newConjuncts) 
        }
        case ts@TupleSelect(e1,index) => {
         val (newargs,newcjs) = flattenArgs(Seq(e1))
          var newConjuncts = newcjs

          val freshArg = newargs(0)
          val newTS = TupleSelect(freshArg, index)
          val freshResVar = Variable(TVarFactory.createTemp("ts").setType(ts.getType))
          newConjuncts += Equals(freshResVar, newTS)           

          (freshResVar, newConjuncts) 
        }
        case cc@CaseClass(cd, args) => {

          val (newargs,newcjs) = flattenArgs(args)
          var newConjuncts = newcjs

          val newCC = CaseClass(cd, newargs)
          val freshResVar = Variable(TVarFactory.createTemp("cc").setType(cc.getType))
          newConjuncts += Equals(freshResVar, newCC)

          (freshResVar, newConjuncts)  
        }
        case tp@Tuple(args) => {
          val (newargs,newcjs) = flattenArgs(args)
          var newConjuncts = newcjs

          val newTP = Tuple(newargs)
          val freshResVar = Variable(TVarFactory.createTemp("tp").setType(tp.getType))
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
                val freshArgVar = Variable(TVarFactory.createTemp("arg").setType(arg.getType))                                           
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
   * Assumption:
   *  (a) the formula does not have match constructs
   * Some important features.
   * (a) For a strict inequality with real variables/constants, the following produces a strict inequality
   * (b) Strict inequalities with only integer variables/constants are reduced to non-strict inequalities 
   */
  def TransformNot(expr: Expr, retainNEQ : Boolean = false): Expr = { // retainIff : Boolean = false
    def nnf(inExpr: Expr): Expr = {
      if(inExpr.getType != BooleanType) inExpr
      else inExpr match {
        //matches integer binary relation
        case Not(e @ BinaryOperator(e1, e2, op)) => {
          if (e1.getType == BooleanType || e1.getType == Int32Type || e1.getType == RealType) {          
            e match {
              case e: Equals => {
                if(retainNEQ) Not(Equals(e1,e2))
                else Or(nnf(LessThan(e1, e2)), nnf(GreaterThan(e1, e2)))
              }
              case e: LessThan => GreaterEquals(nnf(e1), nnf(e2))
              case e: LessEquals => GreaterThan(nnf(e1), nnf(e2))
              case e: GreaterThan => LessEquals(nnf(e1), nnf(e2))
              case e: GreaterEquals => LessThan(nnf(e1), nnf(e2))
              case e: Implies => And(nnf(e1), nnf(Not(e2)))
              case e: Iff => Or(And(nnf(e1), nnf(Not(e2))), And(nnf(e2), nnf(Not(e1))))
              case _ => throw IllegalStateException("Unknown binary operation: " + e)
            }
          }          
          else{
            //in this case e is a binary operation over ADTs
            e match {
              case ninst @ Not(CaseClassInstanceOf(cd, e1)) => Not(CaseClassInstanceOf(cd,nnf(e1)))
              case e: Equals => Not(Equals(nnf(e1),nnf(e2)))
              case _ => throw IllegalStateException("Unknown operation on algebraic data types: " + e)
            } 
          }
        }
        case Not(Not(e1)) => nnf(e1)    
        case e @ Not(t: Terminal) => e
        case e @ Not(FunctionInvocation(_,_)) => e 
        case Not(And(args)) => Or(args.map(arg => nnf(Not(arg))))
        case Not(Or(args)) => And(args.map(arg => nnf(Not(arg))))            
        case Implies(lhs,rhs) => {
          nnf(Or(Not(lhs),rhs))
        }                
        case Iff(lhs,rhs) => {
          //if(retainIff) Iff(nnf(lhs),nnf(rhs)) 
          nnf(And(Implies(lhs,rhs),Implies(rhs,lhs)))
        }
        case Not(IfExpr(cond, thn, elze)) => IfExpr(nnf(cond), nnf(Not(thn)), nnf(Not(elze)))
        case Not(Let(i, v, e)) => Let(i, nnf(v), nnf(Not(e)))
        //note that Not(LetTuple) is not possible 
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
  
  
  def classSelToCons(e: Expr) : Expr = {
    val (r,cd,ccvar,ccfld) = e match {
      case Equals(r0 @ Variable(_), CaseClassSelector(cd0, ccvar0, ccfld0)) => (r0, cd0, ccvar0, ccfld0)
      case Iff(r0 @ Variable(_), CaseClassSelector(cd0, ccvar0, ccfld0)) => (r0, cd0, ccvar0, ccfld0)
      case _ => throw IllegalStateException("Not a case-class-selector call")
    }
    //convert this to a cons by creating dummy variables        
    val args = cd.fieldsIds.map((fld) => {
      if (fld == ccfld) r
      else {
        //create a dummy identifier there
        TVarFactory.createDummy.setType(fld.getType).toVariable
      }
    })
    Equals(ccvar, CaseClass(cd, args))    
  }
  
  def tupleSelToCons(e: Expr) : Expr = {
    val (r,tpvar,index) = e match {
      case Equals(r0 @ Variable(_), TupleSelect(tpvar0, index0)) => (r0, tpvar0, index0)
      case Iff(r0 @ Variable(_), TupleSelect(tpvar0, index0)) => (r0, tpvar0, index0)
      case _ => throw IllegalStateException("Not a tuple-selector call")
    }
    //convert this to a Tuple by creating dummy variables        
    val tupleType = tpvar.getType.asInstanceOf[TupleType]
    val args = (1 until tupleType.dimension + 1).map((i) => {
      if (i == index) r
      else {
        //create a dummy identifier there (note that here we have to use i-1)
        TVarFactory.createDummy.setType(tupleType.bases(i - 1)).toVariable
      }
    })
    Equals(tpvar, Tuple(args))   
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
  
  
  /**
   * A hacky way to implement subexpression check. 
   * TODO: fix this
   */
  def isSubExpr(key: Expr, expr: Expr) : Boolean = {
    
    var found = false
    simplePostTransform((e : Expr) => e match {
      case _ if(e == key) => found = true; e
      case _ => e
    })(expr)
    found
  }
  
  /**
   * Some simplification rules (keep adding more and more rules)
   */
   def simplify(expr: Expr) : Expr = {
        
     //Note: some simplification are already performed by the class constructors (see Tree.scala) 
    simplePostTransform((e : Expr) => e match {
      case Equals(lhs,rhs) if (lhs == rhs) => tru
      case LessEquals(lhs,rhs) if (lhs == rhs) => tru
      case GreaterEquals(lhs,rhs) if (lhs == rhs) => tru
      case LessThan(lhs,rhs) if (lhs == rhs) => fls
      case GreaterThan(lhs,rhs) if (lhs == rhs) => fls
      case Iff(lhs,rhs) if (lhs == rhs) => tru
      case UMinus(IntLiteral(v)) => IntLiteral(-v)
      case Equals(IntLiteral(v1),IntLiteral(v2)) => BooleanLiteral(v1 == v2)
      case LessEquals(IntLiteral(v1),IntLiteral(v2)) => BooleanLiteral(v1 <= v2)
      case LessThan(IntLiteral(v1),IntLiteral(v2)) => BooleanLiteral(v1 < v2)
      case GreaterEquals(IntLiteral(v1),IntLiteral(v2)) => BooleanLiteral(v1 >= v2)
      case GreaterThan(IntLiteral(v1),IntLiteral(v2)) => BooleanLiteral(v1 > v2)    
      case _ => e
    })(expr)    
  }
    
  

  /**
   * Input expression is assumed to be in nnf form
   * Note: (a) Not(Equals()) and Not(Variable) is allowed  
   */
  def isDisjunct(e: Expr): Boolean = e match {
    case And(args) => args.foldLeft(true)((acc, arg) => acc && isDisjunct(arg))
    case Not(Equals(_,_)) | Not(Variable(_)) => true    
    case Or(_) | Implies(_,_) | Iff(_,_) | Not(_)  => false
    case _ => true
  }

  /**
   * assuming that the expression is in nnf form
   * Note: (a) Not(Equals()) and Not(Variable) is allowed 
   */
  def isConjunct(e: Expr): Boolean = e match {
    case Or(args) => args.foldLeft(true)((acc, arg) => acc && isConjunct(arg))
    case Not(Equals(_,_)) | Not(Variable(_)) => true    
    case And(_) | Implies(_,_) | Iff(_,_) | Not(_)  => false
    case _ => true
  }
  
  
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