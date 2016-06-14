package leon
package synthesis.disambiguation

import purescala.Expressions._
import purescala.ExprOps
import purescala.Constructors._
import purescala.Extractors._
import purescala.Types.{ TupleType, BooleanType}
import purescala.Common.{Identifier, FreshIdentifier}
import purescala.Definitions.{FunDef, Program, ValDef}
import purescala.DefOps
import scala.collection.mutable.ListBuffer
import leon.purescala.Definitions.TypedFunDef
import leon.verification.VerificationContext
import leon.verification.VerificationPhase
import leon.solvers._
import scala.concurrent.duration._
import leon.verification.VCStatus
import leon.verification.VCResult
import leon.evaluators.AbstractEvaluator
import java.util.IdentityHashMap
import leon.utils.Position
import scala.collection.JavaConversions._

case class InputNotCoveredException(msg: String, lineExpr: Identifier) extends Exception(msg)

/**
 * @author Mikael
 * If possible, synthesizes a set of inputs for the function so that they cover all parts of the function.
 * 
 * @param fds The set of functions to cover
 * @param fd The calling function
 */
class InputCoverage(fd: FunDef, fds: Set[FunDef])(implicit c: LeonContext, p: Program) {

  /** If set, performs a cleaning up step to cover the whole function */
  var minimizeExamples: Boolean = true
  
  /** Triggers mapping recording between each expression in the bodies of the functions and the example which triggers its computation. */
  def recordMapping() = { doRecordMapping = true; this }
  
  /** Returns a mapping from the expressions in the source code to the set of inputs that cover them
   *  Call `.recordMapping()` before calling `.result()` to have it filled. */
  def getRecordMapping(): IdentityHashMap[Expr, Set[Seq[Expr]]] = {
    var res = new IdentityHashMap[Expr, Set[Seq[Expr]]]()
    for((expr, setFlags) <- flagMapping) {
      res.put(expr, setFlags.flatMap(flag =>
        if(!recordedMapping.containsKey(flag)) {
          throw new Exception(s"No expression associated to $flag")
        } else
        recordedMapping.get(flag)))
    }
    res
  }
  
  /** If true, for each expression in the bodies of the functions, record which example triggers it.*/
  private var doRecordMapping: Boolean = false
  
  /** Mapping from identifiers of lines of code to the input that are covering them.*/
  private var recordedMapping = new IdentityHashMap[Identifier, Set[Seq[Expr]]]()
  
  /** Mapping between every expression and its flag that triggers its computation.*/
  private var flagMapping = new IdentityHashMap[Expr, Set[Identifier]]()
  
  /** If the sub-branches contain identifiers, it returns them unchanged.
      Else it creates a new boolean indicating this branch. */
  private def wrapBranch(e: (Expr, Option[Seq[Identifier]])): (Expr, Some[Seq[Identifier]]) = e._2 match {
    case None =>
      val lineColumnId = FreshIdentifier("l" + Math.abs(e._1.getPos.line) + "c" + Math.abs(e._1.getPos.col), BooleanType).copiedFrom(e._1)
      recordMapping(lineColumnId, e._1)
      (tupleWrap(Seq(e._1, Variable(lineColumnId))), Some(Seq(lineColumnId)))
    case Some(Seq()) =>
      val lineColumnId = FreshIdentifier("l" + Math.abs(e._1.getPos.line) + "c" + Math.abs(e._1.getPos.col), BooleanType).copiedFrom(e._1)
      
      def putInLastBody(expr: Expr): Expr = { recordMapping(lineColumnId, expr); expr } match {
        case Tuple(Seq(v, prev_b)) => Tuple(Seq(v, or(prev_b, lineColumnId.toVariable))).copiedFrom(expr)
        case LetTuple(binders, value, body) => letTuple(binders, value, putInLastBody(body)).copiedFrom(expr)
        case MatchExpr(scrut, Seq(MatchCase(TuplePattern(optId, binders), None, rhs))) => 
          MatchExpr(scrut, Seq(MatchCase(TuplePattern(optId, binders), None, putInLastBody(rhs)))).copiedFrom(expr)
        case FunctionInvocation(tfd, args) => 
          val default_type = tfd.returnType match {
            case TupleType(Seq(t, BooleanType)) =>
              t
            case t => throw new Exception(s"Did not expect function $tfd to return something else than a tuple of a type and a boolean. Got $t")
          }
          val arg_id = FreshIdentifier("arg", default_type)
          val arg_b = FreshIdentifier("bd", BooleanType)
          letTuple(Seq(arg_id, arg_b), expr, Tuple(Seq(arg_id.toVariable, or(arg_b.toVariable, lineColumnId.toVariable))))
        case _ => throw new Exception(s"Unexpected branching case: $expr")
      }
      (putInLastBody(e._1), Some(Seq(lineColumnId)))
    case e_2: Some[_] =>
      // No need to introduce a new boolean since if one of the child booleans is true, then this IfExpr has been called.
      (e._1, e_2)
  }
  
  private def recordMapping(flag: Identifier, expr: Expr): Unit = {
    if(doRecordMapping) {
      val flags: Set[Identifier] = Option(flagMapping.get(expr)).getOrElse(Set()) + flag
      flagMapping.put(expr, flags)
    }
  }
  
  private def recordMapping(flags: Option[Seq[Identifier]], expr: Expr): Unit = {
    if(doRecordMapping) {
      for{flagsC <- flags
          id <- flagsC} {
        recordMapping(id, expr)
      }
    }
    expr match {
      case i: IfExpr =>
      case m: MatchExpr =>
      case Operator(es, builder) =>
        for(e <- es) recordMapping(flags, e)
    }
  }
  
  private def recordExample(input: Seq[Expr], flags: Set[Identifier]): Unit = {
    if(doRecordMapping) {
      for{flag <- flags} {
        val newMappings: Set[Seq[Expr]] = Option(recordedMapping.get(flag)).getOrElse(Set()) + input
        recordedMapping.put(flag, newMappings)
      }
    }
  }
  
  /** Returns true if there are some branching to monitor in the expression */
  private def hasConditionals(e: Expr) = {
    ExprOps.exists{ case i:IfExpr => true case m: MatchExpr => true case f: FunctionInvocation if fds(f.tfd.fd) || f.tfd.fd == fd => true case _ => false}(e)
  }
  
  /** Merges two set of identifiers.
   *  None means that the attached expression is the original one,
   *  Some(ids) means that it has been augmented with booleans and ids are the "monitoring" boolean flags. */
  private def merge(a: Option[Seq[Identifier]], b: Option[Seq[Identifier]]) = {
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
  private def markBranches(e: Expr): (Expr, Option[Seq[Identifier]]) =
    if(!hasConditionals(e)) (e, None) else e match {
    case IfExpr(cond, thenn, elze) =>
      val (c1, cv1) = markBranches(cond)
      val (t1, tv1) = wrapBranch(markBranches(thenn))
      val (e1, ev1) = wrapBranch(markBranches(elze))
      recordMapping(tv1, thenn)
      recordMapping(ev1, elze)
      val mergedIds = merge(merge(cv1, tv1), ev1)
      recordMapping(mergedIds, cond)
      recordMapping(mergedIds, e)
      cv1 match {
        case None =>
          (IfExpr(c1, t1, e1).copiedFrom(e), mergedIds)
        case cv1 =>
          val arg_id = FreshIdentifier("arg", BooleanType)
          val arg_b = FreshIdentifier("bc", BooleanType)
          (letTuple(Seq(arg_id, arg_b), c1, IfExpr(Variable(arg_id), t1, e1).copiedFrom(e)).copiedFrom(e), mergedIds)
      }
    case m@MatchExpr(scrut, cases) =>
      val (c, ids) = markBranches(ExprOps.matchToIfThenElse(m)) // And replace the last error else statement with a dummy flag.
      def replaceFinalElse(e: Expr): (Expr, Identifier)= e match {
        case IfExpr(c1, t1, e1) =>
          val (newElse, id) = replaceFinalElse(e1)
          (IfExpr(c1, t1, newElse).copiedFrom(e), id)
        case Tuple(Seq(Error(tpe, msg), Variable(i))) =>
          (Tuple(Seq(Error(tpe, msg), BooleanLiteral(false))), i)
      }
      val (new_c, id_to_remove) = replaceFinalElse(c)
      (new_c, ids.map(_.filter(_ != id_to_remove)))
    case Or(args) if args.length >= 1 =>
      val c = args.foldRight[Expr](BooleanLiteral(false).copiedFrom(e)){
        case (arg, prev) =>
          IfExpr(arg, BooleanLiteral(true), prev).copiedFrom(e)
      }
      markBranches(c.copiedFrom(e))
    case And(args) if args.length >= 1  =>
      val c = args.foldRight[Expr](BooleanLiteral(true).copiedFrom(e)){
        case (arg, prev) =>
          IfExpr(Not(arg), BooleanLiteral(false), prev).copiedFrom(e)
      }
      markBranches(c.copiedFrom(e))
      
    case Operator(lhsrhs, builder) =>
      // The exprBuilder adds variable definitions needed to compute the arguments.
      val (exprBuilder, children, tmpIds, ids) = (((e: Expr) => e, ListBuffer[Expr](), ListBuffer[Identifier](), None: Option[Seq[Identifier]]) /: lhsrhs) {
        case ((exprBuilder, children, tmpIds, ids), arg) =>
          val (arg1, argv1) = markBranches(arg)
          recordMapping(argv1, arg)
          if(argv1.nonEmpty || isNewFunCall(arg1)) {
            val arg_id = FreshIdentifier("arg", arg.getType)
            val arg_b = FreshIdentifier("ba", BooleanType)
            val f = (body: Expr) => letTuple(Seq(arg_id, arg_b), arg1, body).copiedFrom(body)
            (exprBuilder andThen f, children += Variable(arg_id), tmpIds += arg_b, merge(ids, argv1))
          } else {
            (exprBuilder, children += arg, tmpIds, ids)
          }
      }
      recordMapping(ids, e)
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
              (exprBuilder(funCall), merge(Some(Seq()), ids))
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
  
  /** The cache of transforming functions.*/
  private var cache = Map[FunDef, FunDef]()
  
  /** Records all booleans serving to identify which part of the code should be executed.*/
  private var booleanFlags = Seq[Identifier]()
  
  /** Augment function definitions which should have boolean markers, leave others untouched. */
  private def wrapFunDef(f: FunDef): FunDef = {
    if(!(cache contains f)) {
      if(fds(f) || f == fd) {
        val new_fd = f.duplicate(returnType = TupleType(Seq(f.returnType, BooleanType)))
        new_fd.body = None
        cache += f -> new_fd
        val (new_body, bvars) = wrapBranch(markBranches(f.body.get)) // Recursive call.
        new_fd.body = Some(new_body) // TODO: Handle post-condition if they exist.
        booleanFlags ++= bvars.get
      } else {
        cache += f -> f
      }
    }
    cache(f)
  }
  
  /** Returns true if the expression is a function call with a new function already. */
  private def isNewFunCall(e: Expr): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, targs), args) =>
      cache.values.exists { f => f == fd }
    case _ => false
  }
  
  /** Returns a stream of covering inputs for the function `f`,
   *  such that if `f` is evaluated on each of these inputs, all parts of `{ f } U fds` will have been executed at least once.
   *  
   *  The number of expressions in each element is the same as the number of arguments of `f` */
  def result(): Stream[Seq[Expr]] = {
    cache = Map()
    booleanFlags = Seq()
    recordedMapping = new IdentityHashMap[Identifier, Set[Seq[Expr]]]()
    flagMapping = new IdentityHashMap[Expr, Set[Identifier]]()
    /* Approximative algorithm Algorithm:
     * In innermost branches, replace each result by (result, bi) where bi is a boolean described later.
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
     * Let B be the set of bi.
     *    For each b in B
     *      Set all b' in B to false except b to true
     *      Find a counter-example.
     *      yield  it in the stream.
     */
    
    /* Change all return types to accommodate the new covering boolean */
    
    val transformer = DefOps.funDefReplacer({
      (f: FunDef) =>
        if((fds contains f) || f == fd) {
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

    val program = DefOps.transformProgram(transformer, p)
    
    val start_fd = transformer.transform(fd)
    
    var coveredBooleans = Set[Identifier]()
    // For each boolean flag, set it to true, and find a counter-example which should reach this line.
    // For each new counter-example, abstract evaluate the original function to remove booleans which have been reached.
    val covering_examples =
      for(bvar <- booleanFlags.toStream if !coveredBooleans(bvar)) yield {
      val transformer2 = DefOps.funDefReplacer {
        (f: FunDef) =>
          if(ExprOps.exists { case Variable(id) => booleanFlags contains id case _ => false }(f.fullBody)) {
            val new_f = f.duplicate()
            new_f.fullBody = ExprOps.preMap {
                case Variable(id) if id == bvar => Some(BooleanLiteral(true))
                case Variable(id) if booleanFlags contains id => Some(BooleanLiteral(false))
                case _ => None
            }(f.fullBody)
            Some(new_f)
          } else None

      }
      val program2 = DefOps.transformProgram(transformer2, program)
      val start_fd2 = transformer2.transform(start_fd)
      val tfactory = SolverFactory.getFromSettings(c, program2).withTimeout(10.seconds)
      
      val vctx = new VerificationContext(c, program2, tfactory)
      val vcs = VerificationPhase.generateVCs(vctx, Seq(start_fd2))
      VerificationPhase.checkVCs(vctx, vcs).results(vcs(0)) match {
        case Some(VCResult(VCStatus.Invalid(model), _, _)) => 
          val finalExprs = fd.paramIds.map(model)
          val whoIsEvaluated = functionInvocation(start_fd, finalExprs)
          val ae = new AbstractEvaluator(c, p)
          val coveredFlagsByCounterExample = ae.eval(whoIsEvaluated).result match {
            case Some((Tuple(Seq(_, booleans)), _)) =>
              val targettedIds = ExprOps.collect{ case Variable(id) => Set(id) case _ => Set[Identifier]() }(booleans)
              coveredBooleans ++= targettedIds
              targettedIds
            case _ =>
              Set(bvar)
          }
          //println(s"Recording the example $finalExprs covering $coveredFlagsByCounterExample")
          recordExample(finalExprs, coveredFlagsByCounterExample)
          finalExprs -> coveredFlagsByCounterExample
        case e =>
          throw InputNotCoveredException("Could not find an input to cover the line: " + bvar.getPos.line + " (at col " + bvar.getPos.col + ")\n" + e.getOrElse(""), bvar)
      }
    }
    
    val covering_examples2 = if(minimizeExamples) {
      // Remove examples whose coverage set is included in some other example.
      for((covering_example, flags_met) <- covering_examples
          if !covering_examples.exists{
            case (other_example, other_flags) =>
              other_example != covering_example &&
              flags_met.subsetOf(other_flags)
          }
      ) yield covering_example
    } else {
      covering_examples.map(_._1)
    }
    
    covering_examples2 filter (_.nonEmpty)
  }
}
