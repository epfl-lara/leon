/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Types._
import leon.utils.DebugSectionSynthesis


/**
 * @author Mikael
 */
case object StringRender extends Rule("StringRender") {
  
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    p.xs match {
      case List(IsTyped(v, StringType)) =>
        val description = "Creates a standard string conversion function"
        
        p.as match {
          case List(IsTyped(a, WithStringconverter(converter))) => // Standard conversions if they work.
            List(new RuleInstantiation(description) { // TODO: Use a VSA to ask questions.
              def apply(hctx: SearchContext): RuleApplication = {
                // TODO: Test if the straightforward solution works ! This is wrong for now.
                RuleClosed(Solution(pre=p.pc, defs=Set(), term=converter(Variable(a))))
              }
            })
          /*case List(IsTyped(a, tpe)) =>
            List(new RuleInstantiation(description) {
              def apply(hctx: SearchContext): RuleApplication = {
                val examplesFinder = new ExamplesFinder(hctx.context, hctx.program)
                val examples = examplesFinder.extractFromProblem(p)
                RuleFailed()
              }
            })*/
          case _ =>
            Nil
        }
        
      case _ => Nil
    }
  }
}