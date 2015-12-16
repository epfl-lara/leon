/* Copyright 2009-2015 EPFL, Lausanne */
package leon
package synthesis
package disambiguation

import leon.LeonContext
import leon.purescala.Expressions._
import purescala.Common.FreshIdentifier
import purescala.Constructors.{ and, tupleWrap }
import purescala.Definitions.{ FunDef, Program, ValDef }
import purescala.ExprOps.expressionToPattern
import purescala.Expressions.{ BooleanLiteral, Equals, Expr, Lambda, MatchCase, Passes, Variable, WildcardPattern }
import purescala.Extractors.TopLevelAnds
import leon.purescala.Expressions._

/**
 * @author Mikael
 */
class ExamplesAdder(ctx0: LeonContext, program: Program) {
  
  /** Accepts the nth alternative of a question (0 being the current one) */
  def acceptQuestion[T <: Expr](fd: FunDef, q: Question[T], alternativeIndex: Int): Unit = {
    val newIn  = tupleWrap(q.inputs)
    val newOut = if(alternativeIndex == 0) q.current_output else q.other_outputs(alternativeIndex - 1)
    addToFunDef(fd, Seq((newIn, newOut)))
  }
  
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
                //ctx0.reporter.info("No top-level passes in postcondition, adding it:  " + fd)
              } else {
                val newPasses = exprs(i) match {
                  case Passes(in, out, cases) =>
                    Passes(in, out, (cases ++ newCases).distinct )
                  case _ => ???
                }
                val newPost = and(exprs.updated(i, newPasses) : _*)
                fd.postcondition = Some(Lambda(Seq(ValDef(id, tpe)), newPost))
                //ctx0.reporter.info("Adding the example to the passes postcondition: " + fd)
              }
          }
        } else {
          fd.postcondition = Some(Lambda(Seq(ValDef(id, tpe)), and(post, Passes(inputVariables, Variable(id), newCases))))
          //ctx0.reporter.info("No passes in postcondition, adding it:" + fd)
        }
      case None =>
        val id = FreshIdentifier("res", fd.returnType, false)
        fd.postcondition = Some(Lambda(Seq(ValDef(id, false)), Passes(inputVariables, Variable(id), newCases)))
        //ctx0.reporter.info("No postcondition, adding it: " + fd)
    }
    fd.body match { // TODO: Is it correct to discard the choose construct inside the body?
      case Some(Choose(Lambda(Seq(ValDef(id, tpe)), bodyChoose))) => fd.body = Some(Hole(id.getType, Nil))
      case _ =>
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