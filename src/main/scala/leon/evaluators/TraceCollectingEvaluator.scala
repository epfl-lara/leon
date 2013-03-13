package leon
package evaluators

import purescala.Common._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.Trees._
import purescala.TypeTrees._

import xlang.Trees._

/**
 * @author Ravi
 */
class TraceCollectingEvaluator(ctx : LeonContext, prog : Program) extends Evaluator(ctx, prog) {
  val name = "Trace collecting evaluator"
  val description = "Recursive interpreter for PureScala expressions that keeps of the execution trace"

  private def typeErrorMsg(tree : Expr, expected : TypeTree) : String = "Type error : expected %s, found %s.".format(expected, tree)
  private case class EvalError(msg : String) extends Exception
  private case class RuntimeError(msg : String) extends Exception

  private val maxSteps = 50000  

  def eval(expression: Expr, mapping : Map[Identifier,Expr]) : EvaluationResult = {
    var left: Int = maxSteps
    
    //debugging 
    ctx.reporter.info("collecting execution traces...");
    
    //a symbolic evaluation of an expression 
    case class SymVal(guard :List[Expr], value: Expr)

    /**   
     * The result of rec is a pair of expression and SymVal, the expression is the result of evaluation 
     * which is a constant, the SymVal is the result of symbolic evaluation of the expression which 
     * corresponds to the strongest postcondition of the (concrete) path exercised by the input.
     */    
    def rec(ctx: Map[Identifier,Expr], expr: Expr) : (Expr,SymVal) = if(left <= 0) {
      throw RuntimeError("Diverging computation.")
    } else {
      val fal = BooleanLiteral(false)
      val tru = BooleanLiteral(true)
      
      // println("Step on : " + expr)
      // println(ctx)
      left -= 1
      expr match {
        case Variable(id) => {
          if(ctx.isDefinedAt(id)) {
            val res = ctx(id)
            if(!isGround(res)) {
              throw EvalError("Substitution for identifier " + id.name + " is not ground.")
            } else {              
              (res,SymVal(List[Expr](),Variable(id)))              
            }
          } else {
            throw EvalError("No value for identifier " + id.name + " in mapping.")
          }
        }
        case Tuple(ts) => {
          var guard = List[Expr]()
          var list = Seq[Expr]() 
          
          //recursively compute the symbolic and concrete values of all the elements of the tuple
          val tsRec = ts.map(x => { 
            val res = rec(ctx, x)
            guard = guard ++ res._2.guard
            list = list :+ res._2.value
            res._1
          })         
          (Tuple(tsRec),SymVal(guard,Tuple(list)))
        }
        
        case TupleSelect(t, i) => {
          val (cval,sval) = rec(ctx, t)
          val Tuple(bs) = sval.value
          val Tuple(rs) = cval 
          (rs(i-1),SymVal(sval.guard,bs(i-1)))
        }
        
        case Let(i,e,b) => {          
          val (cval,sval) = rec(ctx, e)
          val (cval2,sval2) = rec(ctx + ((i -> cval)), b)
          val guard = (sval.guard :+ Equals(Variable(i),sval.value)) ++ sval2.guard          
          (cval2,SymVal(guard,sval2.value))          
        }
        
        case Error(desc) => throw RuntimeError("Error reached in evaluation: " + desc)
        case IfExpr(cond, then, elze) => {          
          val (cval,sval) = rec(ctx, cond)
          cval match {
            case BooleanLiteral(true) => {
             val (cval2,sval2) = rec(ctx, then)
             (cval2,SymVal(sval.guard ++ sval2.guard :+ sval.value,sval2.value))
            }
            case BooleanLiteral(false) => {
             val (cval2,sval2) = rec(ctx, elze)
             (cval2,SymVal(sval.guard ++ sval2.guard :+ Not(sval.value), sval2.value))
            }
            case _ => throw EvalError(typeErrorMsg(cval, BooleanType))
          }
        }
        case Waypoint(_, arg) => throw EvalError("Waypoint not handled")
        case FunctionInvocation(fd, args) => {
         
          var guard = List[Expr]()
          var svalList = Seq[Expr]() 
          
          //recursively compute the symbolic and concrete values of all the arguments
          val evArgs = args.map(x => { 
            val (cval,sval) = rec(ctx, x)
            guard =  guard ++ sval.guard
            svalList = svalList :+ sval.value
            cval
          }) 
          
          if(!fd.hasBody && !mapping.isDefinedAt(fd.id)) {
            throw EvalError("Evaluation of function with unknown implementation.")
          }
          //create a new function body that uses new local variable names and parameter names
          val newparams = fd.args.map(x => Variable(FreshIdentifier(x.id.name, true).setType(x.id.getType)))
          val argmap = Map[Identifier,Expr]() ++ (fd.args.map(_.id) zip newparams) 
          							        
          val replacefun  = (e: Expr) => e match { case Variable(id) => argmap.get(id) 
            										case _ => None }
          val funbody = freshenLocals(searchAndReplaceDFS(replacefun)(fd.body.get))
                    
          //rename pre and post conditions
          val precond = if(fd.hasPrecondition) Some(freshenLocals(searchAndReplaceDFS(replacefun)(fd.precondition.get)))
          				else None
          val postcond = if(fd.hasPostcondition) Some(freshenLocals(searchAndReplaceDFS(replacefun)(fd.postcondition.get)))
          				else None
          
          //build a guard mapping parameters to symvals of actual arguments
          val paramguard = (newparams zip svalList).foldLeft(List[Expr]())((g,elem)=> g :+ Equals(elem._1,elem._2))
          var callerguard = guard ++ paramguard
                    
          // build a concrete mapping for the function...
          val frame = Map[Identifier,Expr]((newparams.map(_.id) zip evArgs) : _*)                   
          
          //handle precondition here
          if(precond.isDefined) {
            val (preCval,preSval) = rec(frame, matchToIfThenElse(precond.get)) 
             preCval match {
              case BooleanLiteral(true) => callerguard = callerguard ++ preSval.guard :+ preSval.value //update caller guard
              case BooleanLiteral(false) => {
                throw RuntimeError("Precondition violation for " + fd.id.name + " reached in evaluation.: " + precond.get)
              }
              case other => throw RuntimeError(typeErrorMsg(other, BooleanType))
            }
          }

          val (cres,sres) = rec(frame, matchToIfThenElse(funbody))
         
          //create a new variable to store the return value (this is necessary to handle post-condition)
          val freshResID = FreshIdentifier("r",true).setType(fd.returnType)
          val resvar = Variable(freshResID)
          var calleeguard = sres.guard :+ Equals(resvar,sres.value)

          //handle postcondition here
          if(postcond.isDefined) {
            
            val postBody = replace(Map(ResultVariable() -> resvar), matchToIfThenElse(postcond.get))
            val (postCval,postSval) = rec(frame + ((freshResID -> cres)), postBody)
            postCval match {
              case BooleanLiteral(true) => calleeguard = calleeguard ++ postSval.guard :+ postSval.value
              case BooleanLiteral(false) => throw RuntimeError("Postcondition violation for " + fd.id.name + " reached in evaluation.")
              case other => throw EvalError(typeErrorMsg(other, BooleanType))
            }
          }
          //construct a final guard
          val composedguard = callerguard ++ calleeguard
          (cres,SymVal(composedguard,resvar))
        }
        
        //because of the recursuve 
        case And(args) if args.isEmpty => {           
          (tru,SymVal(List[Expr](),tru))
        }
        
        case And(args) => {          
          val (cval,sval) = rec(ctx, args.head)
           cval match {            
            case BooleanLiteral(false) => {              
              (fal,SymVal(sval.guard,sval.value))
            }
            case BooleanLiteral(true) => {
            	val (cval2,sval2) = rec(ctx, And(args.tail))
            	val guard = sval.guard ++ sval2.guard
            	(cval2,SymVal(guard,And(sval.value,sval2.value)))
            }
            case other => throw EvalError(typeErrorMsg(other, BooleanType))
          }
        }
        case Or(args) if args.isEmpty => (fal,SymVal(List[Expr](),fal))
        case Or(args) => {
          val (cval,sval) = rec(ctx, args.head)
           cval match {
            case BooleanLiteral(true) => {            	
            	(tru,SymVal(sval.guard,sval.value))
            }
            case BooleanLiteral(false) => {
            	val (cval2,sval2) = rec(ctx, And(args.tail))
            	//note that guard only keep tracks of the facts that hold
            	val guard = sval.guard ++ sval2.guard
            	(cval2,SymVal(guard,Or(sval.value,sval2.value)))
            }
            case other => throw EvalError(typeErrorMsg(other, BooleanType))
          }          
        }
        
        case Not(arg) =>  {          
          val (cval,sval) = rec(ctx, arg)
           cval match {
            case BooleanLiteral(v) => (BooleanLiteral(!v),SymVal(sval.guard,Not(sval.value)))            
            case other => throw EvalError(typeErrorMsg(other, BooleanType))
          }          
        }
        
        case Implies(l,r) => rec(ctx,Or(Not(l),r)) 
          
        case Iff(le,re) => rec(ctx,And(Implies(le,re),Implies(re,le)))
        
        /*case Implies(l,r) => (rec(ctx,l), rec(ctx,r)) match {
          case (BooleanLiteral(b1),BooleanLiteral(b2)) => BooleanLiteral(!b1 || b2)
          case (le,re) => throw EvalError(typeErrorMsg(le, BooleanType))
        }
        case Iff(le,re) => (rec(ctx,le),rec(ctx,re)) match {
          case (BooleanLiteral(b1),BooleanLiteral(b2)) => BooleanLiteral(b1 == b2)
          case _ => throw EvalError(typeErrorMsg(le, BooleanType))
        }*/
        
        case Equals(le,re) => {
          val (lc,ls) = rec(ctx,le)
          val (rc,rs) = rec(ctx,re)
          val guard = ls.guard ++ rs.guard
          val value = Equals(ls.value,rs.value)
          val symval = SymVal(guard,value)
            
          (lc,rc) match {
            case (FiniteSet(el1),FiniteSet(el2)) => throw EvalError("Ecountered finite set case in equals")
                     //(BooleanLiteral(el1.toSet == el2.toSet),symval)
            case (FiniteMap(el1),FiniteMap(el2)) => throw EvalError("Ecountered finite map case in equals") 
              //(BooleanLiteral(el1.toSet == el2.toSet),symval)
            case _ => (BooleanLiteral(lc == rc), symval)
          }
        }
        
        case CaseClass(cd, args) => {
          var guard = List[Expr]()
          var svalList = Seq[Expr]() 
          
          //recursively compute the symbolic and concrete values of all the arguments of the constructor
          val evArgs = args.map(x => {  
            val (cval,sval) = rec(ctx, x)
            guard = guard ++ sval.guard
            svalList = svalList :+ sval.value
            cval
          })          
          (CaseClass(cd,evArgs),SymVal(guard,CaseClass(cd,svalList)))           
        }         
        case CaseClassInstanceOf(cd, expr) => {
          val (cval,sval) = rec(ctx,expr)
          val symval = SymVal(sval.guard,CaseClassInstanceOf(cd, sval.value))
          cval.getType match {
            case CaseClassType(cd2) if cd2 == cd => (tru,symval)
            case _ => (fal,symval)
          }          
        }        
        case CaseClassSelector(cd, expr, sel) => {
          val (cval,sval) = rec(ctx,expr)          
          cval match {
            case CaseClass(cd2, args) if cd == cd2 => {              
              val index = cd.selectorID2Index(sel)
              val cres = args(index)
              //val CaseClass(cd3,evArgs) = sval.value
              
              /*if(!cd3.equals(cd2))
                throw EvalError("types of concrete and symbolic values did not match, contype: "
                    +CaseClassType(cd2)+", symtype: "+CaseClassType(cd3))*/
              
              //val sres = evArgs(index)
              (cres,SymVal(sval.guard,CaseClassSelector(cd,sval.value,sel)))
            }
            case _ => throw EvalError(typeErrorMsg(cval, CaseClassType(cd)))
          }
        }
        
        case Plus(l,r) => {         
          val (lc,ls) = rec(ctx,l)
          val (rc,rs) = rec(ctx,r)          
          val symval = SymVal(ls.guard ++ rs.guard,Plus(ls.value,rs.value))
          (lc,rc) match {
          	case (IntLiteral(i1), IntLiteral(i2)) => (IntLiteral(i1 + i2),symval)
          	case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
          }
        }        
        case Minus(l,r) => {
          val (lc,ls) = rec(ctx,l)
          val (rc,rs) = rec(ctx,r)          
          val symval = SymVal(ls.guard ++ rs.guard,Minus(ls.value,rs.value))  
          (lc,rc) match {
          	case (IntLiteral(i1), IntLiteral(i2)) => (IntLiteral(i1 - i2),symval)
          	case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
          }
        }
        case UMinus(e) => {
          val (c,s) = rec(ctx,e)                    
          val symval = SymVal(s.guard,UMinus(s.value))
          c match {          
            case IntLiteral(i) => (IntLiteral(-i),symval)
            case re => throw EvalError(typeErrorMsg(re, Int32Type))
          }          
        }
        case Times(l,r) => {
          val (lc,ls) = rec(ctx,l)
          val (rc,rs) = rec(ctx,r)          
          val symval = SymVal(ls.guard ++ rs.guard,Times(ls.value,rs.value))  
          (lc,rc) match {
          case (IntLiteral(i1), IntLiteral(i2)) => (IntLiteral(i1 * i2),symval)
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        	}
      	}
        case Division(l,r) => {
          val (lc,ls) = rec(ctx,l)
          val (rc,rs) = rec(ctx,r)          
          val symval = SymVal(ls.guard ++ rs.guard,Division(ls.value,rs.value))  
          (lc,rc) match {
          	case (IntLiteral(i1), IntLiteral(i2)) =>
             if(i2 != 0) (IntLiteral(i1 / i2),symval) else throw RuntimeError("Division by 0.")
          	case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
          }
        }
        case Modulo(l,r) => {
          val (lc,ls) = rec(ctx,l)
          val (rc,rs) = rec(ctx,r)          
          val symval = SymVal(ls.guard ++ rs.guard,Modulo(ls.value,rs.value))  
          (lc,rc) match {
          	case (IntLiteral(i1), IntLiteral(i2)) =>
             if(i2 != 0) (IntLiteral(i1 % i2),symval) else throw RuntimeError("Modulo by 0.")
          	case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
          }
        }
        case LessThan(l,r) => {
          val (lc,ls) = rec(ctx,l)
          val (rc,rs) = rec(ctx,r)          
          val symval = SymVal(ls.guard ++ rs.guard,LessThan(ls.value,rs.value))  
          (lc,rc) match {
          	case (IntLiteral(i1), IntLiteral(i2)) => (BooleanLiteral(i1 < i2),symval) 
          	case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
          }
        } 
        case GreaterThan(l,r) => {
          val (lc,ls) = rec(ctx,l)
          val (rc,rs) = rec(ctx,r)          
          val symval = SymVal(ls.guard ++ rs.guard,GreaterThan(ls.value,rs.value))  
          (lc,rc) match {
          	case (IntLiteral(i1), IntLiteral(i2)) => (BooleanLiteral(i1 > i2),symval) 
          	case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
          }
        } 
        case LessEquals(l,r) => {
          val (lc,ls) = rec(ctx,l)
          val (rc,rs) = rec(ctx,r)          
          val symval = SymVal(ls.guard ++ rs.guard,LessEquals(ls.value,rs.value))  
          (lc,rc) match {
          	case (IntLiteral(i1), IntLiteral(i2)) => (BooleanLiteral(i1 <= i2),symval) 
          	case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
          }
        } 
        case GreaterEquals(l,r) => {
          val (lc,ls) = rec(ctx,l)
          val (rc,rs) = rec(ctx,r)          
          val symval = SymVal(ls.guard ++ rs.guard,GreaterEquals(ls.value,rs.value))  
          (lc,rc) match {
          	case (IntLiteral(i1), IntLiteral(i2)) => (BooleanLiteral(i1 >= i2),symval) 
          	case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
          }
        } 

        /*case SetUnion(s1,s2) => (rec(ctx,s1), rec(ctx,s2)) match {
          case (f@FiniteSet(els1),FiniteSet(els2)) => FiniteSet((els1 ++ els2).distinct).setType(f.getType)
          case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
        }
        case SetIntersection(s1,s2) => (rec(ctx,s1), rec(ctx,s2)) match {
          case (f@FiniteSet(els1),FiniteSet(els2)) => {
            val newElems = (els1.toSet intersect els2.toSet).toSeq
            val baseType = f.getType.asInstanceOf[SetType].base
            FiniteSet(newElems).setType(f.getType)
          }
          case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
        }
        case SetDifference(s1,s2) => (rec(ctx,s1), rec(ctx,s2)) match {
          case (f@FiniteSet(els1),FiniteSet(els2)) => {
            val newElems = (els1.toSet -- els2.toSet).toSeq
            val baseType = f.getType.asInstanceOf[SetType].base
            FiniteSet(newElems).setType(f.getType)
          }
          case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
        }
        case ElementOfSet(el,s) => (rec(ctx,el), rec(ctx,s)) match {
          case (e, f @ FiniteSet(els)) => BooleanLiteral(els.contains(e))
          case (l,r) => throw EvalError(typeErrorMsg(r, SetType(l.getType)))
        }
        case SetCardinality(s) => {
          val sr = rec(ctx, s)
          sr match {
            case FiniteSet(els) => IntLiteral(els.size)
            case _ => throw EvalError(typeErrorMsg(sr, SetType(AnyType)))
          }
        }
*/
        //case f @ FiniteSet(els) => FiniteSet(els.map(rec(ctx,_)).distinct).setType(f.getType)
        case i @ IntLiteral(_) => (i,SymVal(List[Expr](),i))
        case b @ BooleanLiteral(_) => (b,SymVal(List[Expr](),b))
        case u @ UnitLiteral => (u,SymVal(List[Expr](),u))

        /*case f @ ArrayFill(length, default) => {
          val rDefault = rec(ctx, default)
          val rLength = rec(ctx, length)
          val IntLiteral(iLength) = rLength
          FiniteArray((1 to iLength).map(_ => rDefault).toSeq)
        }
        case ArrayLength(a) => {
          var ra = rec(ctx, a)
          while(!ra.isInstanceOf[FiniteArray])
            ra = ra.asInstanceOf[ArrayUpdated].array
          IntLiteral(ra.asInstanceOf[FiniteArray].exprs.size)
        }
        case ArrayUpdated(a, i, v) => {
          val ra = rec(ctx, a)
          val ri = rec(ctx, i)
          val rv = rec(ctx, v)

          val IntLiteral(index) = ri
          val FiniteArray(exprs) = ra
          FiniteArray(exprs.updated(index, rv))
        }
        case ArraySelect(a, i) => {
          val IntLiteral(index) = rec(ctx, i)
          val FiniteArray(exprs) = rec(ctx, a)
          try {
            exprs(index)
          } catch {
            case e : IndexOutOfBoundsException => throw RuntimeError(e.getMessage)
          }
        }
        case FiniteArray(exprs) => {
          FiniteArray(exprs.map(e => rec(ctx, e)))
        }

        case f @ FiniteMap(ss) => FiniteMap(ss.map{ case (k, v) => (rec(ctx, k), rec(ctx, v)) }.distinct).setType(f.getType)
        case g @ MapGet(m,k) => (rec(ctx,m), rec(ctx,k)) match {
          case (FiniteMap(ss), e) => ss.find(_._1 == e) match {
            case Some((_, v0)) => v0
            case None => throw RuntimeError("Key not found: " + e)
          }
          case (l,r) => throw EvalError(typeErrorMsg(l, MapType(r.getType, g.getType)))
        }
        case u @ MapUnion(m1,m2) => (rec(ctx,m1), rec(ctx,m2)) match {
          case (f1@FiniteMap(ss1), FiniteMap(ss2)) => {
            val filtered1 = ss1.filterNot(s1 => ss2.exists(s2 => s2._1 == s1._1))
            val newSs = filtered1 ++ ss2
            FiniteMap(newSs).setType(f1.getType)
          }
          case (l, r) => throw EvalError(typeErrorMsg(l, m1.getType))
        }
        case i @ MapIsDefinedAt(m,k) => (rec(ctx,m), rec(ctx,k)) match {
          case (FiniteMap(ss), e) => BooleanLiteral(ss.exists(_._1 == e))
          case (l, r) => throw EvalError(typeErrorMsg(l, m.getType))
        }
        case Distinct(args) => {
          val newArgs = args.map(rec(ctx, _))
          BooleanLiteral(newArgs.distinct.size == newArgs.size)
        }*/ 

        case Choose(_, _) =>
          throw EvalError("Cannot evaluate choose.")

        case other => {
          context.reporter.error("Error: don't know how to handle " + other + " in Evaluator.")
          throw EvalError("Unhandled case in Evaluator : " + other) 
        }
      }
    }

    try {
      val (cval,sval) = rec(mapping, expression)
      
      //create a trace
      val freshResID = FreshIdentifier("r",true).setType(expression.getType)
      val resvar = Variable(freshResID)
      val trace = sval.guard :+ Equals(resvar,sval.value)
      
      //print the trace 
      //println(trace)      
      EvaluationSuccessful(And(trace))
    } catch {
      case so: StackOverflowError => EvaluationError("Stack overflow")
      case EvalError(msg) => EvaluationError(msg)              
      case RuntimeError(msg) => EvaluationFailure(msg)
    }
  }

  // quick and dirty.. don't overuse.
  private def isGround(expr: Expr) : Boolean = {
    variablesOf(expr) == Set.empty
  }
}
