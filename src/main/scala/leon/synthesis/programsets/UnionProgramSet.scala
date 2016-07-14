/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis.programsets

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