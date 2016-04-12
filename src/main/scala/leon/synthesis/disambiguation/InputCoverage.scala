package leon
package synthesis.disambiguation

import synthesis.RuleClosed
import synthesis.Solution
import evaluators.DefaultEvaluator
import purescala.Expressions._
import purescala.ExprOps
import purescala.Constructors._
import purescala.Extractors._
import purescala.Types.{TypeTree, TupleType, BooleanType}
import purescala.Common.{Identifier, FreshIdentifier}
import purescala.Definitions.{FunDef, Program, TypedFunDef}
import purescala.DefOps
import grammars.ValueGrammar
import bonsai.enumerators.MemoizedEnumerator
import solvers.Model
import solvers.ModelBuilder
import scala.collection.mutable.ListBuffer
import leon.LeonContext
import leon.purescala.Definitions.TypedFunDef

/**
 * @author Mikael
 * If possible, synthesizes a set of inputs for the function so that they cover all parts of the function.
 * 
 * @param fds The set of functions to cover
 * @param fd The calling function
 */
class InputCoverage(fd: FunDef, fds: Set[FunDef])(implicit c: LeonContext, p: Program) {
  var numToCoverForEachExample: Int = 1
  
  /** If the sub-branches contain identifiers, it returns them unchanged.
      Else it creates a new boolean indicating this branch. */
  def wrapBranch(e: (Expr, Seq[Identifier])): (Expr, Seq[Identifier]) = {
    if(e._2.isEmpty) { // No need to introduce a new boolean since if one of the child booleans is true, then this IfExpr has been called.
      val b = FreshIdentifier("l" + e._1.getPos.line + "c" + e._1.getPos.col)
      (tupleWrap(Seq(e._1, Variable(b))), Seq(b))
    } else e
  }
  
  def hasConditionals(e: Expr) = {
    ExprOps.exists{ case i:IfExpr => true case m: MatchExpr => true case f: FunctionInvocation => true case _ => false}(e)
  }
  
  /** For each branch in the expression, adds a boolean variable such that the new type of the expression is (previousType, Boolean)
   *  If no variable is output, then the type of the expression is not changed.
    * Returns the list of boolean variables which appear in the expression */
  // All functions now return a boolean along with their original return type.
  def markBranches(e: Expr): (Expr, Seq[Identifier]) =
    if(!hasConditionals(e)) (e, Seq()) else e match {
    case IfExpr(cond, thenn, elze) =>
      val (c1, cv1) = markBranches(cond)
      val (t1, tv1) = wrapBranch(markBranches(thenn))
      val (e1, ev1) = wrapBranch(markBranches(elze))
      // TODO: Deal with the case when t1 and e1 is empty.
      (IfExpr(c1, t1, e1).copiedFrom(e), cv1 ++ tv1 ++ ev1)
    case MatchExpr(scrut, cases) =>
      val (c1, cv1) = markBranches(scrut)
      val (new_cases, variables) = (cases map { case MatchCase(pattern, opt, rhs) =>
        val (rhs_new, ids) = wrapBranch(markBranches(rhs))
        (MatchCase(pattern, opt, rhs_new), ids)
      }).unzip // TODO: Check for unapply with function pattern ?
      (MatchExpr(c1, new_cases).copiedFrom(e), variables.flatten)
    case Operator(lhsrhs, builder) =>
      // The exprBuilder adds variable definitions needed to compute the arguments.
      val (exprBuilder, children, ids) = (((e: Expr) => e, List[Expr](), ListBuffer[Identifier]()) /: lhsrhs) {
        case ((exprBuilder, children, ids), arg) =>
          val (arg1, argv1) = markBranches(arg)
          if(argv1.nonEmpty) {
            val arg_id = FreshIdentifier("arg", arg.getType)
            val arg_b = FreshIdentifier("b", BooleanType)
            val f = (body: Expr) => letTuple(Seq(arg_id, arg_b), arg1, body)
            (exprBuilder andThen f, Variable(arg_id)::children, ids ++= argv1)
          } else {
            (exprBuilder, arg::children, ids)
          }
      }
      e match {
        case FunctionInvocation(TypedFunDef(fd, targs), args) =>
          // Should be different since functions will return a boolean as well.
          val res_id = FreshIdentifier("res", fd.returnType)
          val res_b = FreshIdentifier("b", BooleanType)
          val finalIds = (ids :+ res_b)
          val finalExpr = 
            tupleWrap(Seq(Variable(res_id), or(finalIds.map(Variable(_)): _*)))
          val funCall = letTuple(Seq(res_id, res_b), builder(children).copiedFrom(e), finalExpr)
          (exprBuilder(funCall), finalIds)
        case _ =>
          if(ids.isEmpty) {
            (e, Seq.empty)
          } else {
            val finalExpr = tupleWrap(Seq(builder(children).copiedFrom(e), or(ids.map(Variable): _*)))
            (exprBuilder(finalExpr), ids)
          }
      }
  }
  
  /** The number of expressions is the same as the number of arguments. */
  def result(): Stream[Seq[Expr]] = {
    /* Algorithm:
     * def f(x: Int, z: Boolean): Int =
     *   x match {
     *     case 0 | 1 =>
     *       if(z) f(if(z) x else -x, z) else 1
     *     case _ =>
     *       (if(z) x
     *       else f(x-1,!z)+f(x-2,!z))*f(x-1,!z)
     *   } 
     * 2) In innermost branches, replace each result by (result, bi) where bi is a boolean described later.
     * def f(x: Int, z: Boolean): (Int, Boolean) =
     *   x match {
     *     case 0 | 1 =>
     *       if(z) {
     *         ({val (r, b1) = if(z) (x, bt) else (-x, be)
     *         val (res, b) = f(r, z)
     *         (res, b || b1)
     *     case _ =>
     *       val (res, b) = if(z) (x, b2)
     *       else (f(x-1,!z)+f(x-2,!z), b3)
     *       (res*f(x-1,!z), b)
     *   } 
     * 3) If the function is recursive, recover the previous values and left-OR them with the returning bi.
     * def f(x: Int, z: Boolean): (Int, Boolean) =
     *   x match {
     *     case 0 | 1 => (1, b1)
     *     case _ =>
     *       if(z) {
     *         val (r, bf) = f(x-1,!z)
     *         (x*r, b2 || bf)}
     *       else {
     *         val (r, bf) = f(x-1,!z)
     *         val (r2, bf2) = f(x-2,!z)
     *         (r+r2, b3 || bf || bf2)
     *       }
     *   } 
     * 4) Add the post-condition
     *   ensuring { res => !res._2 }
     * 5) Let B be the set of bi.
     *    For each b in B
     *      Set all b' in B to false except b to true
     *      Find a counter-example.
     *      yield  it in the stream.
     */
    
    /* Change all return types to accommodate the new covering boolean */
    val changeReturnTypes = { (p: Program) =>
        val (program, idMap, fdMap, cdMap) = DefOps.replaceFunDefs(p)({
          (f: FunDef) =>
            if((fds contains f) || f == fd) {
              Some(f.duplicate(returnType = TupleType(Seq(f.returnType, BooleanType))))
            } else
              None
        }, {
          (fi: FunctionInvocation, newFd: FunDef) =>
            Some(TupleSelect(FunctionInvocation(newFd.typed, fi.args), 1))
        })
        (program, fdMap(fd), fds.map(fdMap))
    }
    val addNewReturnVariables = { (p: Program, fd: FunDef, fds: Set[FunDef]) => 
      

      
      
    }
    
    (changeReturnTypes andThen
     addNewReturnVariables.tupled)(p)
    
    
    ???
  }
}