/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import bonsai.{Generator => Gen}

object GrammarTag extends Enumeration {
  val Top = Value
}
import GrammarTag._

class Generator[T, R](subTrees: Seq[T], builder: Seq[R] => R, tag: Value) extends Gen[T,R](subTrees, builder)
object Generator {
  def apply[T, R](subTrees: Seq[T], builder: Seq[R] => R, tag: Value = Top) = new Generator(subTrees, builder, tag)
}