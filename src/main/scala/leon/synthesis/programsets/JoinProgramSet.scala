package leon
package synthesis.programsets

import leon.purescala
import purescala.Expressions._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Types._

/**
 * @author Mikael
 */
object JoinProgramSet {
  
  def apply[T, U1, U2](sets: (ProgramSet[U1], ProgramSet[U2]), recombine: (U1, U2) => T): Join2ProgramSet[T, U1, U2] = {
    new Join2ProgramSet(sets, recombine)
  }
  def apply[T, U](sets: Seq[ProgramSet[U]], recombine: Seq[U] => T): JoinProgramSet[T, U] = {
    new JoinProgramSet(sets, recombine)
  }
  def direct[U1, U2](sets: (ProgramSet[U1], ProgramSet[U2])): Join2ProgramSet[(U1, U2), U1, U2] = {
    new Join2ProgramSet(sets, (u1: U1, u2: U2) => (u1, u2))
  }
  def direct[U](sets: Seq[ProgramSet[U]]): JoinProgramSet[Seq[U], U] = {
    new JoinProgramSet(sets, (id: Seq[U]) => id)
  }
}

class Join2ProgramSet[T, U1, U2](sets: (ProgramSet[U1], ProgramSet[U2]), recombine: (U1, U2) => T) extends ProgramSet[T] {
  def programs: Stream[T] = utils.StreamUtils.cartesianProduct(sets._1.programs, sets._2.programs).map(recombine.tupled)
}

class JoinProgramSet[T, U](sets: Seq[ProgramSet[U]], recombine: Seq[U] => T) extends ProgramSet[T] {
  def programs: Stream[T] = utils.StreamUtils.cartesianProduct(sets.map(_.programs)).map(recombine)
}

