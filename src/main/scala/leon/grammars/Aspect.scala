/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Expressions.Expr

/**
 * An Aspect applies to a label, and attaches information to it.
 *
 * For instance, the "size" aspect provides information about the size of
 * expressions the label represents, (displayed as |5|).
 *
 * Int|5| is thus a Label "Int" with aspect "Sized(5)". The applyTo method of
 * the aspect can filter/modify/generate sub-productions:
 * If the grammar contains a Int -> Int + Int production, then
 * Int|5| will generate productions by doing: |5|.applyTo(Int + Int),
 * which itself returns:
 *   - Int|1| + Int|3|
 *   - Int|3| + Int|1|
 *   - Int|2| + Int|2|
 *
 */


abstract class Aspect(val kind: AspectKind) extends Printable {

  final type Production = ProductionRule[Label, Expr]

  def applyTo(l: Label, ps: Seq[Production])(implicit ctx: LeonContext): Seq[Production]
}

sealed abstract class AspectKind(val order: Int) extends Ordered[AspectKind] {
  def compare(that: AspectKind) = this.order-that.order
}

// Order determines the order of application of aspects
case object RealTypedAspectKind         extends AspectKind(10)
case object NamedAspectKind             extends AspectKind(20)
case object DepthBoundAspectKind        extends AspectKind(30)
case object ExtraTerminalsAspectKind    extends AspectKind(40)
case object SimilarToAspectKind         extends AspectKind(50)
case object TypeDepthBoundAspectKind    extends AspectKind(60)
case object SizedAspectKind             extends AspectKind(70)
case object TaggedAspectKind            extends AspectKind(80)

