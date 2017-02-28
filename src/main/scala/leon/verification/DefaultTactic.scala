/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package verification

import purescala.Expressions._
import purescala.ExprOps._
import purescala.Definitions._
import purescala.Constructors._
import purescala.Extractors._
import purescala.Types._
import leon.synthesis.ExamplesFinder

class DefaultTactic(vctx: VerificationContext) extends Tactic(vctx) {
  val description = "Default verification condition generation approach"

  private val strictArithmeticChecking: Boolean =
    ctx.findOptionOrDefault(VerificationPhase.optStrictArithmeticChecking)

  private val overflowChecking: Boolean =
    ctx.findOptionOrDefault(VerificationPhase.optOverflowChecking) || strictArithmeticChecking

  def generatePostconditions(fd: FunDef): Seq[VC] = {
    (fd.postcondition, fd.body) match {
      case (Some(post), Some(body)) =>
        val newpost = if(post match { case Lambda(vd, tla@TopLevelAnds(conjuncts)) => conjuncts.exists(_.isInstanceOf[Passes]) case _ => false}) {
          val ef = new ExamplesFinder(vctx, vctx.program)
          val examples = ef.extractFromFunDef(fd, true)
          val examplesConditions = examples.invalids.collect{
             case synthesis.InOutExample(in, out) =>
               not(and(fd.paramIds.zip(in).map{ idVal => Equals(Variable(idVal._1), idVal._2)}: _*))
          }

          post match {
            case Lambda(vd, tla@TopLevelAnds(conjuncts)) =>
              Lambda(vd, and(examplesConditions ++ conjuncts.filterNot(ExamplesFinder.isConcretelyTestablePasses) :_*).copiedFrom(tla)
              ).copiedFrom(post)
          }}
          else post

        val vc = implies(fd.precOrTrue, application(newpost, Seq(body)))
        Seq(VC(vc, fd, VCKinds.Postcondition).setPos(post))
      case _ =>
        Nil
    }
  }

  def generatePreconditions(fd: FunDef): Seq[VC] = {

    val calls = collectWithPC {
      case c @ FunctionInvocation(tfd, _) if tfd.hasPrecondition =>
        c
    }(fd.fullBody)

    calls.map {
      case (fi @ FunctionInvocation(tfd, args), path) =>
        val pre = tfd.withParamSubst(args, tfd.precondition.get)
        val vc = path implies pre
        val fiS = sizeLimit(fi.asString, 40)
        VC(vc, fd, VCKinds.Info(VCKinds.Precondition, s"call $fiS")).setPos(fi)
    }

  }

  def generateCorrectnessConditions(fd: FunDef): Seq[VC] = {

    def eToVCKind(e: Expr) = e match {
      case _ : MatchExpr =>
        VCKinds.ExhaustiveMatch

      case Assert(_, Some(err), _) =>
        if (err.startsWith("Map ")) {
          VCKinds.MapUsage
        } else if (err.startsWith("Array ")) {
          VCKinds.ArrayUsage
        } else if (err.startsWith("Division ")) {
          VCKinds.DivisionByZero
        } else if (err.startsWith("Modulo ")) {
          VCKinds.ModuloByZero
        } else if (err.startsWith("Remainder ")) {
          VCKinds.RemainderByZero
        } else if (err.startsWith("Cast ")) {
          VCKinds.CastError
        } else {
          VCKinds.Assert
        }

      case BVRemainder(_, _) | BVShiftLeft(_, _) | BVAShiftRight(_, _) | BVLShiftRight(_, _) =>
        VCKinds.StrictArithmetic

      case BVPlus(_, _) | BVMinus(_, _) | BVUMinus(_) | BVDivision(_, _) | BVTimes(_, _) =>
        VCKinds.ArithmeticOverflow

      case _ =>
        VCKinds.Assert
    }

    // We don't collect preconditions here, because these are handled by generatePreconditions
    val calls = collectCorrectnessConditions(fd.fullBody)

    calls.map {
      case (e, correctnessCond) =>
        VC(correctnessCond, fd, eToVCKind(e)).setPos(e)
    }
  }

  private val mask = IntLiteral(0x80000000)
  private def applyMask(a: Expr): Expr = BVAnd(a, mask)

  private def inRange(min: Int, max: Int, e: Expr): Expr = {
    val (minL, maxL) = e.getType match {
      case Int32Type => (IntLiteral(min), IntLiteral(max))
      case t => ctx.reporter.internalError(s"Unexpected type $t")
    }

    and(LessEquals(minL, e), LessEquals(e, maxL))
  }


  /** Collects from within an expression all conditions under which the evaluation of the expression
    * will not fail (e.g. by violating a function precondition or evaluating to an error).
    *
    * Collection of preconditions of function invocations can be disabled
    * (mainly for [[leon.verification.Tactic]]).
    *
    * @param e The expression for which correctness conditions are calculated.
    * @param collectFIs Whether we also want to collect preconditions for function invocations
    * @return A sequence of pairs (expression, condition)
    */
  def collectCorrectnessConditions(e: Expr, collectFIs: Boolean = false): Seq[(Expr, Expr)] = {
    val conds = collectWithPC {

      case m @ MatchExpr(scrut, cases) =>
        (m, orJoin(cases map (matchCaseCondition(scrut, _).toClause)))

      case e @ Error(_, _) =>
        (e, BooleanLiteral(false))

      case a @ Assert(cond, _, _) =>
        (a, cond)

      case e @ BVPlus(x, y) if overflowChecking =>
        val cond = Implies(equality(applyMask(x), applyMask(y)), equality(applyMask(x), applyMask(e)))
        (e, cond)

      case e @ BVMinus(x, y) if overflowChecking =>
        val cond = Implies(not(equality(applyMask(x), applyMask(y))), equality(applyMask(x), applyMask(e)))
        (e, cond)

      case e @ BVTimes(x, y) if overflowChecking =>
        val cond = or(equality(x, IntLiteral(0)), equality(BVDivision(BVTimes(x,y), x), y))
        (e, cond)

      case e @ BVDivision(x, y) if overflowChecking =>
        assert(x.getType == Int32Type) // other kind of bv not covered here
        val cond = not(and(equality(x, IntLiteral(Int.MinValue)), equality(y, IntLiteral(-1))))
        (e, cond)

      // This is not really an overflow, but rather a limitation of C so we treat it as a strict arithmetic problem
      case e @ BVRemainder(x, y) if strictArithmeticChecking =>
        assert(x.getType == Int32Type) // other kind of bv not covered here
        val cond = not(and(equality(x, IntLiteral(Int.MinValue)), equality(y, IntLiteral(-1))))
        (e, cond)

      case e @ BVUMinus(x) if overflowChecking =>
        assert(x.getType == Int32Type) // other kind of bv not covered here
        val cond = not(equality(x, IntLiteral(Int.MinValue))) // -2^31
        (e, cond)

      case e @ BVShiftLeft(x, y) if strictArithmeticChecking =>
        assert(y.getType == Int32Type) // other kinds of bv shift not covered by this
        val cond = inRange(0, 31, y)
        (e, cond)

      case e @ BVAShiftRight(x, y) if strictArithmeticChecking =>
        assert(y.getType == Int32Type) // other kinds of bv shift not covered by this
        val cond = inRange(0, 31, y)
        (e, cond)

      case e @ BVLShiftRight(x, y) if strictArithmeticChecking =>
        assert(y.getType == Int32Type) // other kinds of bv shift not covered by this
        val cond = inRange(0, 31, y)
        (e, cond)


      /*case e @ Ensuring(body, post) =>
        (e, application(post, Seq(body)))

      case r @ Require(pred, e) =>
        (r, pred)*/

      case fi @ FunctionInvocation(tfd, args) if tfd.hasPrecondition && collectFIs =>
        (fi, tfd.withParamSubst(args, tfd.precondition.get))
    }(e)

    conds map {
      case ((e, cond), path) =>
        (e, path implies cond)
    }
  }

  /* UNUSED
   * def simpleCorrectnessCond(e: Expr, path: Path, sf: SolverFactory[Solver]): Expr = {
   *   simplifyPaths(sf, path)(
   *     andJoin( collectCorrectnessConditions(e) map { _._2 } )
   *   )
   * }
   */

}
