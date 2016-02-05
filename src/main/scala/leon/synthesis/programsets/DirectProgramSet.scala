package leon.synthesis.programsets

import leon.purescala
import purescala.Expressions._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Types._

object DirectProgramSet {
  def apply[T](p: Stream[T]): DirectProgramSet[T] = new DirectProgramSet(p)
}

/**
 * @author Mikael
 */
class DirectProgramSet[T](val p: Stream[T]) extends ProgramSet[T] {
  def programs = p
}