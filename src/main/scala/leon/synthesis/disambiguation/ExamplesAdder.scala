/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package disambiguation

import purescala.Types.FunctionType
import purescala.Common.{FreshIdentifier, Identifier}
import purescala.Constructors.{ and, tupleWrap }
import purescala.Definitions.{ FunDef, Program, ValDef }
import purescala.ExprOps
import purescala.Extractors.TopLevelAnds
import purescala.Expressions._
import leon.utils.Simplifiers

/**
 * @author Mikael
 */
object ExamplesAdder {
  def replaceGenericValuesByVariable(e: Expr): (Expr, Map[Expr, Expr]) = {
    var assignment = Map[Expr, Expr]()
    var extension = 'a'
    var id = ""
    (ExprOps.postMap({ expr => expr match {
      case g@GenericValue(tpe, index) => 
        val newIdentifier = FreshIdentifier(tpe.id.name.take(1).toLowerCase() + tpe.id.name.drop(1) + extension + id, tpe.id.getType)
        if(extension != 'z' && extension != 'Z')
          extension = (extension.toInt + 1).toChar
        else if(extension == 'z')  // No more than 52 generic variables in practice?
          extension = 'A'
        else {
          if(id == "") id = "1" else id = (id.toInt + 1).toString
        }
        
        val newVar = Variable(newIdentifier)
        assignment += g -> newVar
        Some(newVar)
      case _ => None
    } })(e), assignment)
  }
}

class ExamplesAdder(ctx0: LeonContext, program: Program) {
  import ExamplesAdder._
  var _removeFunctionParameters = false
  
  def setRemoveFunctionParameters(b: Boolean) = { _removeFunctionParameters = b; this }
  
  /** Accepts the nth alternative of a question (0 being the current one) */
  def acceptQuestion[T <: Expr](fd: FunDef, q: Question[T], alternativeIndex: Int): Unit = {
    val newIn  = tupleWrap(q.inputs)
    val newOut = if(alternativeIndex == 0) q.current_output else q.other_outputs(alternativeIndex - 1)
    addToFunDef(fd, Seq((newIn, newOut)))
  }
  
  private def filterCases(cases: Seq[MatchCase]) = cases.filter(c => c.optGuard != Some(BooleanLiteral(false)))
  
  def addToExpr(_post: Expr, id: Identifier, inputVariables: Expr, newCases: Seq[MatchCase]): Expr = {
    val post=  Simplifiers.bestEffort(ctx0, program)(_post)
    if(purescala.ExprOps.exists(_.isInstanceOf[Passes])(post)) {
      post match {
        case TopLevelAnds(exprs) =>
          val i = exprs.lastIndexWhere { x => x match {
            case Passes(in, out, cases) if in == inputVariables && out == Variable(id) => true
            case _ => false
          } }
          if(i == -1) {
            Lambda(Seq(ValDef(id)), and(post, Passes(inputVariables, Variable(id), newCases)))
            //ctx0.reporter.info("No top-level passes in postcondition, adding it:  " + fd)
          } else {
            val newPasses = exprs(i) match {
              case Passes(in, out, cases) =>
                Passes(in, out, (filterCases(cases) ++ newCases).distinct )
              case _ => ???
            }
            val newPost = and(exprs.updated(i, newPasses) : _*)
            Lambda(Seq(ValDef(id)), newPost)
            //ctx0.reporter.info("Adding the example to the passes postcondition: " + fd)
          }
      }
    } else {
      Lambda(Seq(ValDef(id)), and(post, Passes(inputVariables, Variable(id), newCases)))
      //ctx0.reporter.info("No passes in postcondition, adding it:" + fd)
    }
    
    
  }
  
  /** Adds the given input/output examples to the function definitions */
  def addToFunDef(fd: FunDef, examples: Seq[(Expr, Expr)]): Unit = {
    val params = if(_removeFunctionParameters) fd.params.filter(x => !x.getType.isInstanceOf[FunctionType]) else fd.params
    val inputVariables = tupleWrap(params.map(p => Variable(p.id): Expr))
    val newCases = examples.map{ case (in, out) => exampleToCase(in, out) }
    fd.postcondition match {
      case Some(Lambda(Seq(ValDef(id)), post)) =>
        fd.postcondition = Some(addToExpr(post, id, inputVariables, newCases))
      case None =>
        val id = FreshIdentifier("res", fd.returnType, false)
        fd.postcondition = Some(addToExpr(BooleanLiteral(true), id, inputVariables, newCases))
    }
    fd.body match { // TODO: Is it correct to discard the choose construct inside the body?
      case Some(Choose(Lambda(Seq(ValDef(id)), bodyChoose))) =>
        fd.body = Some(Choose(addToExpr(bodyChoose, id, inputVariables, newCases)))
      case _ =>
    }
  }
  
  private def exampleToCase(in: Expr, out: Expr): MatchCase = {
    val (inPattern, inGuard) = ExprOps.expressionToPattern(in)
    if(inGuard == BooleanLiteral(true)) {
      MatchCase(inPattern, None, out)
    } else /*if (in == in_raw) { } *else*/ {
      val id = FreshIdentifier("out", in.getType, true)
      MatchCase(WildcardPattern(Some(id)), Some(Equals(Variable(id), in)), out)
    }
  }
 }
