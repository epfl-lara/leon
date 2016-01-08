package leon
package synthesis.programsets

import leon.purescala
import purescala.Expressions._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Types._

object UnionProgramSet {
  def apply[T](sets: Seq[ProgramSet[T]]): UnionProgramSet[T] = {
    new UnionProgramSet(sets)
  }
}

/**
 * @author Mikael
 */
class UnionProgramSet[T](sets: Seq[ProgramSet[T]]) extends ProgramSet[T] {
  def programs = utils.StreamUtils.interleave(sets.map(_.programs))
}