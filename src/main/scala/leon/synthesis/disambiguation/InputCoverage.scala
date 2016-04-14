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
import purescala.Definitions.{FunDef, Program, TypedFunDef, ValDef}
import purescala.DefOps
import grammars.ValueGrammar
import bonsai.enumerators.MemoizedEnumerator
import solvers.Model
import solvers.ModelBuilder
import scala.collection.mutable.ListBuffer
import leon.LeonContext
import leon.purescala.Definitions.TypedFunDef
import leon.verification.VerificationContext
import leon.verification.VerificationPhase
import leon.solvers._
import scala.concurrent.duration._
import leon.verification.VCStatus
import leon.verification.VCResult

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
  def wrapBranch(e: (Expr, Option[Seq[Identifier]])): (Expr, Some[Seq[Identifier]]) = e._2 match {
    case None =>
      val b = FreshIdentifier("l" + Math.abs(e._1.getPos.line) + "c" + Math.abs(e._1.getPos.col), BooleanType)
      (tupleWrap(Seq(e._1, Variable(b))), Some(Seq(b)))
    case Some(Seq()) =>
      val b = FreshIdentifier("l" + Math.abs(e._1.getPos.line) + "c" + Math.abs(e._1.getPos.col), BooleanType)
      
      def putInLastBody(e: Expr): Expr = e match {
        case Tuple(Seq(v, prev_b)) => Tuple(Seq(v, or(prev_b, b.toVariable))).copiedFrom(e)
        case LetTuple(binders, value, body) => letTuple(binders, value, putInLastBody(body)).copiedFrom(e)
        case MatchExpr(scrut, Seq(MatchCase(TuplePattern(optId, binders), None, rhs))) => 
          MatchExpr(scrut, Seq(MatchCase(TuplePattern(optId, binders), None, putInLastBody(rhs)))).copiedFrom(e)
        case _ => throw new Exception(s"Unexpected branching case: $e")
        
      }
      (putInLastBody(e._1), Some(Seq(b)))
    case e_2: Some[_] =>
      // No need to introduce a new boolean since if one of the child booleans is true, then this IfExpr has been called.
      (e._1, e_2)
  }
  
  def hasConditionals(e: Expr) = {
    ExprOps.exists{ case i:IfExpr => true case m: MatchExpr => true case f: FunctionInvocation => true case _ => false}(e)
  }
  
  def merge(a: Option[Seq[Identifier]], b: Option[Seq[Identifier]]) = {
    (a, b) match {
      case (None, None) => None
      case (a, None) => a
      case (None, b) => b
      case (Some(a), Some(b)) => Some(a ++ b)
    }
  }
  
  /** For each branch in the expression, adds a boolean variable such that the new type of the expression is (previousType, Boolean)
   *  If no variable is output, then the type of the expression is not changed.
    * If the expression is augmented with a boolean, returns the list of boolean variables which appear in the expression */
  // All functions now return a boolean along with their original return type.
  def markBranches(e: Expr): (Expr, Option[Seq[Identifier]]) =
    if(!hasConditionals(e)) (e, None) else e match {
    case IfExpr(cond, thenn, elze) =>
      val (c1, cv1) = markBranches(cond)
      val (t1, tv1) = wrapBranch(markBranches(thenn))
      val (e1, ev1) = wrapBranch(markBranches(elze))
      cv1 match {
        case None =>
          (IfExpr(c1, t1, e1).copiedFrom(e), merge(tv1, ev1))
        case cv1 =>
          val arg_id = FreshIdentifier("arg", BooleanType)
          val arg_b = FreshIdentifier("bc", BooleanType)
          (letTuple(Seq(arg_id, arg_b), c1, IfExpr(Variable(arg_id), t1, e1).copiedFrom(e)).copiedFrom(e), merge(merge(cv1, tv1), ev1))
      }
    case MatchExpr(scrut, cases) =>
      val (c1, cv1) = markBranches(scrut)
      val (new_cases, variables) = (cases map { case m@MatchCase(pattern, opt, rhs) =>
        val (rhs_new, ids) = wrapBranch(markBranches(rhs))
        (MatchCase(pattern, opt, rhs_new).copiedFrom(m), ids)
      }).unzip // TODO: Check for unapply with function pattern ?
      (MatchExpr(c1, new_cases).copiedFrom(e), variables.fold(None)(merge))
    case Operator(lhsrhs, builder) =>
      // The exprBuilder adds variable definitions needed to compute the arguments.
      val (exprBuilder, children, tmpIds, ids) = (((e: Expr) => e, ListBuffer[Expr](), ListBuffer[Identifier](), None: Option[Seq[Identifier]]) /: lhsrhs) {
        case ((exprBuilder, children, tmpIds, ids), arg) =>
          val (arg1, argv1) = markBranches(arg)
          if(argv1.nonEmpty || isNewFunCall(arg1)) {
            val arg_id = FreshIdentifier("arg", arg.getType)
            val arg_b = FreshIdentifier("ba", BooleanType)
            val f = (body: Expr) => letTuple(Seq(arg_id, arg_b), arg1, body).copiedFrom(body)
            (exprBuilder andThen f, children += Variable(arg_id), tmpIds += arg_b, merge(ids, argv1))
          } else {
            (exprBuilder, children += arg, tmpIds, ids)
          }
      }
      e match {
        case FunctionInvocation(tfd@TypedFunDef(fd, targs), args) if fds(fd) =>
          val new_fd = wrapFunDef(fd)
          // Is different since functions will return a boolean as well.
          tmpIds match {
            case Seq() =>
              val funCall = FunctionInvocation(TypedFunDef(new_fd, targs).copiedFrom(tfd), children).copiedFrom(e)
              (exprBuilder(funCall), if(new_fd != fd) merge(Some(Seq()), ids) else ids)
            case idvars =>
              val res_id = FreshIdentifier("res", fd.returnType)
              val res_b = FreshIdentifier("bb", BooleanType)
              val finalIds = idvars :+ res_b
              val finalExpr = 
                tupleWrap(Seq(Variable(res_id), or(finalIds.map(Variable(_)): _*))).copiedFrom(e)
              val funCall = letTuple(Seq(res_id, res_b), FunctionInvocation(TypedFunDef(new_fd, targs), children).copiedFrom(e), finalExpr).copiedFrom(e)
              (exprBuilder(funCall), Some(finalIds))
          }
        case _ =>
          tmpIds match {
            case Seq() =>
              (e, ids)
            case idvars =>
              val finalExpr = tupleWrap(Seq(builder(children).copiedFrom(e), or(idvars.map(Variable): _*))).copiedFrom(e)
              (exprBuilder(finalExpr), ids)
          }
      }
  }
  
  // The cache of transforming functions.
  var cache = Map[FunDef, FunDef]()
  
  // Records all boolean serving to identify which part of the code should be executed.
  var booleanFlags = Seq[Identifier]()
  
  def wrapFunDef(fd: FunDef): FunDef = {
    if(!(cache contains fd)) {
      if(fds(fd)) {
        val new_fd = fd.duplicate(returnType = TupleType(Seq(fd.returnType, BooleanType)))
        new_fd.body = None
        cache += fd -> new_fd
        val (new_body, bvars) = wrapBranch(markBranches(fd.body.get)) // Recursive call.
        new_fd.body = Some(new_body) // TODO: Handle post-condition if they exist.
        booleanFlags ++= bvars.get
      } else {
        cache += fd -> fd
      }
    }
    cache(fd)
  }
  
  def isNewFunCall(e: Expr): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, targs), args) =>
      cache.values.exists { f => f == fd }
    case _ => false
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
    
    val (program, idMap, fdMap, cdMap) = DefOps.replaceFunDefs(p)({
      (f: FunDef) =>
        if((fds contains   f) || f == fd) {
          val new_fd = wrapFunDef(f)
          if(f == fd) {
            val h = FreshIdentifier("h", TupleType(Seq(fd.returnType, BooleanType)), false)
            new_fd.postcondition = Some(Lambda(Seq(ValDef(h)), Not(TupleSelect(Variable(h), 2))))
          }
          Some(new_fd)
        } else
          None
    }, {
      (fi: FunctionInvocation, newFd: FunDef) => //if(cache contains fi.tfd.fd) {
        Some(TupleSelect(FunctionInvocation(newFd.typed, fi.args), 1))
      //} else None
    })
    
    val start_fd = fdMap.getOrElse(fd, fd)
    
    // For each boolean flag, set it to true,
    val covering_examples = for(bvar <- booleanFlags.toStream) yield {
      val (program2, idMap2, fdMap2, cdMap2) = DefOps.replaceFunDefs(program)({
        (f: FunDef) =>
          if(ExprOps.exists(e => e match { case Variable(id) => booleanFlags contains id case _ => false })(f.fullBody)) {
            val new_f = f.duplicate()
            new_f.fullBody = ExprOps.preMap(e => {
              e match {
                case Variable(id) if id == bvar => Some(BooleanLiteral(true))
                case Variable(id) if booleanFlags contains id => Some(BooleanLiteral(false))
                case _ => None
              }
            })(f.fullBody)
            Some(new_f)
          } else None
      })
      val start_fd2 = fdMap2.getOrElse(start_fd, start_fd)
      
      val tfactory = SolverFactory.getFromSettings(c, program2).withTimeout(5.seconds)
      
      val vctx = new VerificationContext(c, program2, tfactory)
      val vcs = VerificationPhase.generateVCs(vctx, Seq(start_fd2))
      VerificationPhase.checkVCs(vctx, vcs).results(vcs(0)) match {
        case None => Seq()
        case Some(VCResult(VCStatus.Invalid(model), _, _)) => 
          fd.paramIds.map(model)
      }
    }
    
    covering_examples filter (_.nonEmpty)
  }
}