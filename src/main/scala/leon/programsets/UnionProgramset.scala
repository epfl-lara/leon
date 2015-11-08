package leon.programsets

import leon.purescala
import purescala.Expressions._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Types._

object UnionProgramSet {
  
  /** Interleaves two streams, ensuring that if both terminate, the resulting stream terminates. */
  def combine[A](sa: Stream[A], sb: Stream[A]): Stream[A] = {
    if(sa.isEmpty) sb else if(sb.isEmpty) sa else sa.head #:: combine(sb, sa.tail)
  }

  /** Interleaves an arbitrary number of streams, ensuring that if all of them terminate, the resulting stream terminates. */
  def combine[A](s: Seq[Stream[A]]): Stream[A] = {
    if(s.isEmpty) Stream.Empty else
    if(s.head.isEmpty) combine(s.tail) else
    s.head.head #:: combine(s.tail ++ Seq(s.head.tail))
  }
}

/**
 * @author Mikael
 */
class UnionProgramset(sets: Seq[ProgramSet]) extends ProgramSet {
  def programs = UnionProgramSet.combine(sets.map(_.programs))
}