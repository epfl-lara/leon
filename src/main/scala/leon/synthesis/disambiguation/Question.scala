package leon
package synthesis.disambiguation

import purescala.Expressions.Expr

/**
 * @author Mikael
 */
case class Question[T <: Expr](inputs: List[Expr], current_output: T, other_outputs: List[T])