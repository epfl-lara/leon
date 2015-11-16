/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Types._
import leon.utils.DebugSectionSynthesis
import leon.purescala.Common.{Identifier, FreshIdentifier}
import leon.purescala.Definitions.FunDef
import leon.utils.IncrementalMap
import leon.purescala.Definitions.FunDef
import leon.purescala.Definitions.ValDef


/**
 * @author Mikael
 */
case object StringRender extends Rule("StringRender") {
  
  var _defaultTypeToString: Option[Map[TypeTree, FunDef]] = None
  
  def defaultMapTypeToString()(implicit hctx: SearchContext): Map[TypeTree, FunDef] = {
    _defaultTypeToString.getOrElse{
      // Updates the cache with the functions converting standard types to string.
      val res = (hctx.program.library.StrOps.toSeq.flatMap { StrOps => 
        StrOps.defs.collect{ case d: FunDef if d.params.length == 1 && d.returnType == StringType => d.params.head.getType -> d }
      }).toMap
      _defaultTypeToString = Some(res)
      res
    }
  }
  
  /** Returns a toString function converter if it has been defined. */
  class WithFunDefConverter(implicit hctx: SearchContext) {
    def unapply(tpe: TypeTree): Option[FunDef] = {
      _defaultTypeToString.flatMap(_.get(tpe))
    }
  }
  
  val e: AbstractClassType = null
  
  /** Returns a seq of expressions such as `x + y + "1" + y + "2" + z` associated to an expected result string `"1, 2"`.
    * We use these equations so that we can find the values of the constants x, y, z and so on.
    * This uses a custom evaluator which does not concatenate string but reminds the calculation.
    */
  def createProblems(inlineFunc: Seq[FunDef], inlineExpr: Expr, examples: ExamplesBank): Seq[(Expr, String)] = ???
  
  /** For each solution to the problem such as `x + "1" + y + j + "2" + z = 1, 2`, outputs all possible assignments if they exist. */
  def solveProblems(problems: Seq[(Expr, String)]): Seq[Map[Identifier, String]] = ???
  
  
  /// Disambiguation: Enumerate different solutions, augment the size of examples by 1, and check discrepancies.
  
  /** Returns a stream of expressions consistent with the specifications. Tail-recursive method*/
  def solve(ADTToString: Map[TypeTree, FunDef], inputs: Seq[(Identifier, TypeTree)], inlineFuns: Seq[FunDef], inlineExpr: Expr, examples: ExamplesBank): Stream[(FunDef, Expr)] = {
    val inputTypeWithoutToStringFunction = inputs.collectFirst{ case (input, tpe: AbstractClassType) if
      WithStringconverter.unapply(tpe).isEmpty &&
      ADTToString.contains(tpe) =>
        (input, tpe)
    }
    
    inputTypeWithoutToStringFunction match {
      case Some((input, tpe)) =>
        val inductOn = FreshIdentifier(input.name, input.getType, true)
        val fd = new FunDef(FreshIdentifier("rec", alwaysShowUniqueID = true),
            Nil, ValDef(inductOn) :: Nil, StringType) // Empty function.
        solve(ADTToString + (tpe -> fd), inputs, inlineFuns ++ Seq(fd), inlineExpr, examples) // Tail recursion.
      case None =>
        // Now all types have a corresponding toString function, even if it is empty for now.
        
        
        
        Stream.Empty
    }
  }
  
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    p.xs match {
      case List(IsTyped(v, StringType)) =>
        val description = "Creates a standard string conversion function"
        
        val defaultToStringFunctions = defaultMapTypeToString()
        
        val examplesFinder = new ExamplesFinder(hctx.context, hctx.program)
        val examples = examplesFinder.extractFromProblem(p)
        
        /** Possible strategies.
          * If data structure is recursive on at least one variable (see how Induction works)
          * then
          *   - Inserts a new rec function deconstructing it and put it into the available preconditions to use.
          * If the input is constant
          *   - just a variable to compute a constant.
          * If there are several variables
          *   - All possible ways of linearly unbuilding the structure
          * if a variable is a primitive
          *   - Introduce an ordered string containing the content.
          *   
          * Once we have a skeleton, we run it on examples given and solve it.
          * If there are multiple solutions, we generate one deeper example and ask the user which one should be better.
          */
        
        /* All input variables which are inductive in the post condition, along with their abstract data type. */

        
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