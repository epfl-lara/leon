/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules.unused

import purescala.Common._
import purescala.Expressions._
import purescala.Extractors._
import purescala.ExprOps._
import purescala.TreeNormalizations.linearArithmeticForm
import purescala.TreeNormalizations.NonLinearExpressionException
import purescala.Types._
import purescala.Constructors._
import purescala.Definitions._
import leon.synthesis.Algebra.lcm

case object IntegerInequalities extends Rule("Integer Inequalities") {
  def instantiateOn(implicit hctx: SearchContext, problem: Problem): Traversable[RuleInstantiation] = {
    val TopLevelAnds(exprs) = problem.phi

    //assume that we only have inequalities
    var lhsSides: List[Expr] = Nil
    var exprNotUsed: List[Expr] = Nil
    //normalized all inequalities to LessEquals(t, 0)
    exprs.foreach{
      case LessThan(a, b) => lhsSides ::= Plus(Minus(a, b), IntLiteral(1))
      case LessEquals(a, b) => lhsSides ::= Minus(a, b)
      case GreaterThan(a, b) => lhsSides ::= Plus(Minus(b, a), IntLiteral(1))
      case GreaterEquals(a, b) => lhsSides ::= Minus(b, a)
      case e => exprNotUsed ::= e
    }

    val ineqVars = lhsSides.foldLeft(Set[Identifier]())((acc, lhs) => acc ++ variablesOf(lhs))
    val nonIneqVars = exprNotUsed.foldLeft(Set[Identifier]())((acc, x) => acc ++ variablesOf(x))
    val candidateVars = ineqVars.intersect(problem.xs.toSet).diff(nonIneqVars)

    val processedVars: Set[(Identifier, Int)] = candidateVars.flatMap(v => {
      try {
        val normalizedLhs: List[List[Expr]] = lhsSides.map(linearArithmeticForm(_, Array(v)).toList)
        if(normalizedLhs.isEmpty)
          Some((v, 0))
        else
          Some((v, lcm(normalizedLhs.map{ case List(t, IntLiteral(i)) => if(i == 0) 1 else i.abs case _ => sys.error("shouldn't happen") })))
      } catch {
        case NonLinearExpressionException(_) =>
          None
      }
    })

    if (processedVars.isEmpty) {
      Nil
    } else {
      val processedVar = processedVars.toList.sortWith((t1, t2) => t1._2 <= t2._2).head._1

      val otherVars: List[Identifier] = problem.xs.filterNot(_ == processedVar)


      val normalizedLhs: List[List[Expr]] = lhsSides.map(linearArithmeticForm(_, Array(processedVar)).toList)
      var upperBounds: List[(Expr, Int)] = Nil // (t, c) means c*x <= t
      var lowerBounds: List[(Expr, Int)] = Nil // (t, c) means t <= c*x
      normalizedLhs.foreach{
        case List(t, IntLiteral(i)) => 
          if(i > 0) upperBounds ::= (expandAndSimplifyArithmetic(UMinus(t)), i)
          else if(i < 0) lowerBounds ::= (expandAndSimplifyArithmetic(t), -i)
          else exprNotUsed ::= LessEquals(t, IntLiteral(0)) //TODO: make sure that these are added as preconditions
        case err => sys.error("unexpected from normal form: " + err)
      }

      val L = if(upperBounds.isEmpty && lowerBounds.isEmpty) -1 else lcm((upperBounds ::: lowerBounds).map(_._2))

      //optimization when coef = 1 and when ub - lb is a constant greater than LCM
      //upperBounds = upperBounds.filterNot{case (ub, uc) => if(uc == 1) {
      //    exprNotUsed ++= lowerBounds.map{case (lb, lc) => LessEquals(lb, Times(IntLiteral(lc), ub))}
      //    true
      //  } else
      //    false
      //}
      //lowerBounds = lowerBounds.filterNot{case (lb, lc) => if(lc == 1) {
      //    exprNotUsed ++= upperBounds.map{case (ub, uc) => LessEquals(Times(IntLiteral(uc), lb), ub)}
      //    true
      //  } else 
      //    false 
      //}
      //upperBounds = upperBounds.filterNot{case (ub, uc) => {
      //  lowerBounds.forall{case (lb, lc) => {
      //    expandAndSimplifyArithmetic(Minus(ub, lb)) match {
      //    case IntLiteral(n) => L - 1 <= n
      //    case _ => false
      //  }}}
      //}}


      //define max function
      val maxValDefs: Seq[ValDef] = lowerBounds.map(_ => ValDef(FreshIdentifier("b", Int32Type)))
      val maxFun = new FunDef(FreshIdentifier("max"), Nil, maxValDefs, Int32Type)
      def maxRec(bounds: List[Expr]): Expr = bounds match {
        case (x1 :: x2 :: xs) => {
          val v = FreshIdentifier("m", Int32Type)
          Let(v, IfExpr(LessThan(x1, x2), x2, x1), maxRec(Variable(v) :: xs))
        }
        case (x :: Nil) => x
        case Nil => sys.error("cannot build a max expression with no argument")
      }
      if(lowerBounds.nonEmpty)
        maxFun.body = Some(maxRec(maxValDefs.map(vd => Variable(vd.id)).toList))
      def max(xs: Seq[Expr]): Expr = FunctionInvocation(maxFun.typed, xs)
      //define min function
      val minValDefs: Seq[ValDef] = upperBounds.map(_ => ValDef(FreshIdentifier("b", Int32Type)))
      val minFun = new FunDef(FreshIdentifier("min"), Nil, minValDefs, Int32Type)
      def minRec(bounds: List[Expr]): Expr = bounds match {
        case (x1 :: x2 :: xs) => {
          val v = FreshIdentifier("m", Int32Type)
          Let(v, IfExpr(LessThan(x1, x2), x1, x2), minRec(Variable(v) :: xs))
        }
        case (x :: Nil) => x
        case Nil => sys.error("cannot build a min expression with no argument")
      }
      if(upperBounds.nonEmpty)
        minFun.body = Some(minRec(minValDefs.map(vd => Variable(vd.id)).toList))
      def min(xs: Seq[Expr]): Expr = FunctionInvocation(minFun.typed, xs)
      val floorFun = new FunDef(FreshIdentifier("floorDiv"), Nil, Seq(
                                        ValDef(FreshIdentifier("x", Int32Type)),
                                        ValDef(FreshIdentifier("x", Int32Type))), Int32Type)
      val ceilingFun = new FunDef(FreshIdentifier("ceilingDiv"), Nil, Seq(
                                        ValDef(FreshIdentifier("x", Int32Type)),
                                        ValDef(FreshIdentifier("x", Int32Type))), Int32Type)
      ceilingFun.body = Some(IntLiteral(0))
      def floorDiv(x: Expr, y: Expr): Expr = FunctionInvocation(floorFun.typed, Seq(x, y))
      def ceilingDiv(x: Expr, y: Expr): Expr = FunctionInvocation(ceilingFun.typed, Seq(x, y))

      val witness: Expr = if(upperBounds.isEmpty) {
        if(lowerBounds.size > 1) max(lowerBounds.map{case (b, c) => ceilingDiv(b, IntLiteral(c))})
        else ceilingDiv(lowerBounds.head._1, IntLiteral(lowerBounds.head._2))
      } else {
        if(upperBounds.size > 1) min(upperBounds.map{case (b, c) => floorDiv(b, IntLiteral(c))})
        else floorDiv(upperBounds.head._1, IntLiteral(upperBounds.head._2))
      }

      if(otherVars.isEmpty) { //here we can simply evaluate the precondition and return a witness

        val constraints: List[Expr] = for((ub, uc) <- upperBounds; (lb, lc) <- lowerBounds) 
                                        yield LessEquals(ceilingDiv(lb, IntLiteral(lc)), floorDiv(ub, IntLiteral(uc)))
        val pre = And(exprNotUsed ++ constraints)
        List(solve(Solution(pre, Set(), tupleWrap(Seq(witness)))))
      } else {

        val involvedVariables = (upperBounds++lowerBounds).foldLeft(Set[Identifier]())((acc, t) => {
          acc ++ variablesOf(t._1)
        }).intersect(problem.xs.toSet) //output variables involved in the bounds of the process variables
        var newPre: Expr = BooleanLiteral(true)
        if(involvedVariables.isEmpty) {
          newPre = And(
            for((ub, uc) <- upperBounds; (lb, lc) <- lowerBounds) 
                yield LessEquals(ceilingDiv(lb, IntLiteral(lc)), floorDiv(ub, IntLiteral(uc)))
          )
          lowerBounds = Nil
          upperBounds = Nil
        }

        val remainderIds: List[Identifier] = upperBounds.map(_ => FreshIdentifier("k", Int32Type, true))
        val quotientIds: List[Identifier] = lowerBounds.map(_ => FreshIdentifier("l", Int32Type, true))

        val newUpperBounds: List[Expr] = upperBounds.map{case (bound, coef) => Times(IntLiteral(L/coef), bound)}
        val newLowerBounds: List[Expr] = lowerBounds.map{case (bound, coef) => Times(IntLiteral(L/coef), bound)}


        val subProblemFormula = expandAndSimplifyArithmetic(And(
          newUpperBounds.zip(remainderIds).zip(quotientIds).flatMap{
            case ((b, k), l) => Equals(b, Plus(Times(IntLiteral(L), Variable(l)), Variable(k))) :: 
                                newLowerBounds.map(lbound => LessEquals(Variable(k), Minus(b, lbound)))
          } ++ exprNotUsed))
        val subProblemxs: List[Identifier] = quotientIds ++ otherVars
        val subProblem = Problem(problem.as ++ remainderIds, problem.ws, problem.pc, subProblemFormula, subProblemxs)

        def onSuccess(sols: List[Solution]): Option[Solution] = sols match {
          case List(s @ Solution(pre, defs, term, isTrusted)) =>
            if(remainderIds.isEmpty) {
              Some(Solution(
                And(newPre, pre),
                defs,
                letTuple(subProblemxs, term,
                  Let(processedVar, witness,
                    tupleWrap(problem.xs.map(Variable)))),
                isTrusted
              ))
            } else if(remainderIds.size > 1) {
              sys.error("TODO")
            } else {
              val k = remainderIds.head
              
              val loopCounter = Variable(FreshIdentifier("i", Int32Type, true))
              val concretePre = replace(Map(Variable(k) -> loopCounter), pre)
              val concreteTerm = replace(Map(Variable(k) -> loopCounter), term)
              val returnType = tupleTypeWrap(problem.xs.map(_.getType))
              val funDef = new FunDef(FreshIdentifier("rec", alwaysShowUniqueID = true), Nil, Seq(ValDef(loopCounter.id)), returnType)
              val funBody = expandAndSimplifyArithmetic(IfExpr(
                LessThan(loopCounter, IntLiteral(0)),
                Error(returnType, "No solution exists"),
                IfExpr(
                  concretePre,
                  letTuple(subProblemxs, concreteTerm,
                    Let(processedVar, witness,
                      tupleWrap(problem.xs.map(Variable)))
                  ),
                  FunctionInvocation(funDef.typed, Seq(Minus(loopCounter, IntLiteral(1))))
                )
              ))
              funDef.body = Some(funBody)

              Some(Solution(And(newPre, pre), defs + funDef, FunctionInvocation(funDef.typed, Seq(IntLiteral(L-1)))))
            }
          case _ =>
            None
        }

        List(decomp(List(subProblem), onSuccess, this.name))
      }
    }
  }
}
