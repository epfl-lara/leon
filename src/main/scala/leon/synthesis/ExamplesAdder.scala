/* Copyright 2009-2015 EPFL, Lausanne */
package leon
package synthesis

import leon.LeonContext
import leon.purescala.Expressions._
import purescala.Common.FreshIdentifier
import purescala.Constructors.{ and, tupleWrap }
import purescala.Definitions.{ FunDef, Program, ValDef }
import purescala.ExprOps.expressionToPattern
import purescala.Expressions.{ BooleanLiteral, Equals, Expr, Lambda, MatchCase, Passes, Variable, WildcardPattern }
import purescala.Extractors.TopLevelAnds


/**
 * @author Mikael
 */
class ExamplesAdder(ctx0: LeonContext, program: Program) {
  
  /** Adds the given input/output examples to the function definitions */
  def addToFunDef(fd: FunDef, examples: Seq[(Expr, Expr)]) = {
    val inputVariables = tupleWrap(fd.params.map(p => Variable(p.id): Expr))
    val newCases = examples.map{ case (in, out) => exampleToCase(in, out) }
    fd.postcondition match {
      case Some(Lambda(Seq(ValDef(id, tpe)), post)) =>
        if(fd.postcondition.exists { e => purescala.ExprOps.exists(_.isInstanceOf[Passes])(e) }) {
          post match {
            case TopLevelAnds(exprs) =>
              val i = exprs.lastIndexWhere { x => x match {
                case Passes(in, out, cases) if in == inputVariables && out == Variable(id) => true
                case _ => false
              } }
              if(i == -1) {
                fd.postcondition = Some(Lambda(Seq(ValDef(id, tpe)), and(post, Passes(inputVariables, Variable(id), newCases))))
              } else {
                val newPasses = exprs(i) match {
                  case Passes(in, out, cases) =>
                    Passes(in, out, cases ++ newCases )
                  case _ => ???
                }
                val newPost = and(exprs.updated(i, newPasses) : _*)
                fd.postcondition = Some(Lambda(Seq(ValDef(id, tpe)), newPost))
              }
          }
        } else {
          fd.postcondition = Some(Lambda(Seq(ValDef(id, tpe)), and(post, Passes(inputVariables, Variable(id), newCases))))
        }
      case None =>
        val id = FreshIdentifier("res", fd.returnType, false)
        fd.postcondition = Some(Lambda(Seq(ValDef(id, None)), Passes(inputVariables, Variable(id), newCases)))
    }
  }
  
  private def exampleToCase(in: Expr, out: Expr): MatchCase = {
    val (inPattern, inGuard) = expressionToPattern(in)
    if(inGuard != BooleanLiteral(true)) {
      val id = FreshIdentifier("out", in.getType, true)
      MatchCase(WildcardPattern(Some(id)), Some(Equals(Variable(id), in)), out)
    } else {
      MatchCase(inPattern, None, out)
    }
  }
 }