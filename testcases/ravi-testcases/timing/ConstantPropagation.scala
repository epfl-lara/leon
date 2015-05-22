import leon.lang._
import leon.annotation._
import leon.collection._
import leon._
import leon.lang.invariantLang._

object IntLattice {

  abstract class Element
  case class Bot() extends Element
  case class Top() extends Element
  case class IntVal(x : Int) extends Element

  def height = {
    /**
     * A number that depends on the lattice definition.
     * In simplest case it has height 3 (_|_ (bot) <= Ints <= T (top))
     */
    3
  }

  def join(oldVal: Element, newVal: Element) = (oldVal, newVal) match {
    case (Bot(), any) => any // bot is the identity for join
    case (any , Bot()) => any
    case (Top(), _) => Top() // top joined with anything is top
    case (_, Top()) => Top()
    case (IntVal(x), IntVal(y)) if(x == y) => IntVal(y)
    case _  =>
      //here old and new vals are different integers
      Top()
  }

  def add(a: Element, b: Element): Element = {
    (a, b) match {
      case (Bot(), _) => Bot()
      case (_, Bot()) => Bot()
      case (Top(), _) => Top()
      case (_, Top()) => Top()
      case (IntVal(x), IntVal(y)) => IntVal(x + y)
    }
  }

  def multiply(a: Element, b: Element): Element = {
    (a, b) match {
      case (_, IntVal(x)) if x == 0 => IntVal(0)
      case (IntVal(x), _) if x == 0 => IntVal(0)
      case (Bot(), _) => Bot()
      case (_, Bot()) => Bot()
      case (Top(), _) => Top()
      case (_, Top()) => Top()
      case (IntVal(x), IntVal(y)) => IntVal(x * y)
    }
  }
}

object ConstantPropagation {
  import IntLattice._

  abstract class Expr
  case class Times(lhs: Expr, rhs: Expr) extends Expr
  case class Plus(lhs: Expr, rhs: Expr) extends Expr
  case class IntLiteral(v: Element) extends Expr
  case class FunctionCall(calleeId :Int, args: List[Expr]) extends Expr

  /**
   * Definition of a function AST
   */
  case class Function(id: Int, params: List[Expr], body: Expr)

  /**
   * Assuming that the functions are ordered from callee to
   * caller and there is no mutual recursion
   */
  case class Program(funcs: List[Function])

  def size(l: List[Function]) : Int = {l match {
    case Cons(_,t) => 1 + size(t)
    case Nil() => 0
  }} 

  def sizeExprList(exprs: List[Expr]): Int = {
    exprs match {
      case Nil() => 0
      case Cons(currExpr, otherExprs) => sizeExpr(currExpr) + sizeExprList(otherExprs)
    }
  } 

  def sizeExpr(e: Expr): Int = {
    e match {
      case Plus(l, r)  => 1 + sizeExpr(l) + sizeExpr(r)
      case Times(l, r) => 1 + sizeExpr(l) + sizeExpr(r)
      case FunctionCall(c, args) => {
        1 + sizeExprList(args)
      }
      case _ => 1
    }
  } 

  def sizeFuncList(funcs: List[Function]): Int = {
    funcs match {
      case Nil() => 0
      case Cons(currFunc, otherFuncs) => 1 + sizeExpr(currFunc.body) + sizeFuncList(otherFuncs)
    }
  } 

  def initToBot(l: List[Function]): List[(Int /*function id*/,Element)] = {
    l match {
      case Nil() => Nil[(Int /*function id*/,Element)]()
      case Cons(fun, tail) => Cons((fun.id, Bot()), initToBot(tail))
    }
  } ensuring (res => true template((a, b) => time <= a*size(l) + b))

  def foldConstants(p : Program): List[(Int /*function id*/,Element)] = {
    //initialize the values of all functions to Bot()
    foldConstantsRec(p, initToBot(p.funcs), height)
  } //ensuring(res => true template((a, b, c) => time <= (height*sizeFuncList(p.funcs))*a + height*b + c))

  /**
   * The initVals is the initial values for the
   * values of the functions
   */
  def foldConstantsRec(p: Program, initVals: List[(Int /*function id*/ , Element)], noIters: Int)
  : List[(Int /*function id*/,Element)] = {
    require(noIters >= 0)
     // if (noIters > 0) {
     //    val newVals = processFuns(p.funcs, initVals, initVals)
     //    if (newVals != initVals) // this  is not a constant time operation
     //      foldConstantsRec(p, newVals, noIters - 1)
     //    else
     //      newVals
     //  } else
     //    initVals
     if (noIters <= 0) {
        initVals
      }
      else
        foldConstantsRec(p, processFuns(p.funcs, initVals, initVals), noIters - 1)
   } ensuring(res => true template((a, b, d) => time <= a*(sizeFuncList(p.funcs)*noIters) + b*noIters + d))
   //c*sizeFuncList(p.funcs) 

  /**
   * Initial fvals and oldVals are the same
   * but as the function progresses, fvals will only have the olds values
   * of the functions that are yet to be processed, whereas oldVals will remain the same.
   */
  def processFuns(funcs: List[Function], fvals : List[(Int, Element)], oldVals: List[(Int, Element)])
  : List[(Int, Element)] = {
    (funcs, fvals) match {
      case (Cons(f, otherFuns), Cons((fid, fval), otherVals)) =>
        val newVal = analyzeFunction(f, oldVals)
        val approxVal = IntLattice.join(fval, newVal) //creates an approximation of newVal to ensure convergence
        Cons((fid, approxVal), processFuns(otherFuns, otherVals, oldVals))
      case  _ =>
        Nil[(Int, Element)]() //this also handles precondition violations e.g. lists aren't of same size etc.
    }
  } ensuring(res => true template((a, b) => time <= a*sizeFuncList(funcs) + b))
  
  @constantTime
  def isConstantCall(args: List[Expr]): Boolean = {
    args match {
      case Nil() => true
      case Cons(IntLiteral(_), otherExprs) => isConstantCall(otherExprs)
      case _ => false
    }
  }

  @constantTime
  def getFunctionVal(funcId: Int, funcVals: List[(Int, Element)]): Element = {
    funcVals match {
      case Nil() => Bot()
      case Cons((currFuncId, currFuncVal), otherFuncVals) if (currFuncId == funcId) => currFuncVal
      case Cons(_, otherFuncVals) => getFunctionVal(funcId, otherFuncVals)
    }
  }

  def foldConstantsExprList(l: List[Expr], funcVals: List[(Int, Element)]): List[Expr] = {
    l match {
      case Nil() => Nil[Expr]()
      case Cons(expr, otherExprs) => Cons(foldConstantsExpr(expr, funcVals), foldConstantsExprList(otherExprs, funcVals))
    }
  } ensuring(res => true template((a, b) => time <= a*sizeExprList(l) + b))

  def foldConstantsExpr(e: Expr, funcVals: List[(Int, Element)]): Expr = {
    e match {
      case Times(lhs: Expr, rhs: Expr) => {
        val foldedLHS = foldConstantsExpr(lhs, funcVals)
        val foldedRHS = foldConstantsExpr(rhs, funcVals)
        (foldedLHS, foldedRHS) match {
          case (IntLiteral(lhsConst), IntLiteral(rhsConst)) => IntLiteral(multiply(lhsConst, rhsConst))
          case _ => Times(foldedLHS, foldedRHS)
        }
      }

      case Plus(lhs: Expr, rhs: Expr) => {
        val foldedLHS = foldConstantsExpr(lhs, funcVals)
        val foldedRHS = foldConstantsExpr(rhs, funcVals)
        (foldedLHS, foldedRHS) match {
          case (IntLiteral(lhsConst), IntLiteral(rhsConst)) => IntLiteral(add(lhsConst, rhsConst))
          case _ => Plus(foldedLHS, foldedRHS)
        }
      }

      case FunctionCall(calleeId, args: List[Expr]) => {
        val foldedArgs = foldConstantsExprList(args, funcVals)
        if (isConstantCall(foldedArgs)) {
          IntLiteral(getFunctionVal(calleeId, funcVals))
        }
        else FunctionCall(calleeId, foldedArgs)
      }
      case _ => e
    }
  } ensuring(res => true template((a, b) => time <= a*sizeExpr(e) + b))

  def analyzeFunction(f: Function, oldVals: List[(Int, Element)]) = {
    // traverse the body of the function and simplify constants
    // for function calls assuming the value given by oldVals
    // also for if-then-else statments, take a join of the values alone if and else branches
    // assume that bot op any = bot and top op any = top (but this can be made more precise).
    val foldedBody = foldConstantsExpr(f.body, oldVals)
    foldedBody match {
      case IntLiteral(funcVal) => funcVal
      case _ => Bot()
    }
  } ensuring(res => true template((a, b) => time <= a*sizeExpr(f.body) + b))
}
