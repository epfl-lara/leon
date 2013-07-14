package leon
package datagen

import purescala.Trees._
import purescala.Common._

trait DataGenerator {
  def generateFor(ins: Seq[Identifier], satisfying: Expr, maxValid: Int, maxEnumerated: Int): Iterator[Seq[Expr]];
}
