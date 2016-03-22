/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis.disambiguation

import purescala.Expressions.Expr

/**
 * @author Mikael
 */
case class Question[T <: Expr](inputs: Seq[Expr], current_output: T, other_outputs: List[T])