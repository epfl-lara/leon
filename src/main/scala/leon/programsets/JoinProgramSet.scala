package leon.programsets

import leon.purescala
import purescala.Expressions._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Types._

object JoinProgramSet {
  
  def cantorPair(x: Int, y: Int): Int = {
    ((x + y) * (x + y + 1)) / 2 + y
  }


  def reverseCantorPair(z: Int): (Int, Int) = {
      val t = Math.floor((-1.0f + Math.sqrt(1.0f + 8.0f * z))/2.0f).toInt;
      val x = t * (t + 3) / 2 - z;
      val y = z - t * (t + 1) / 2;
      (x, y)
  }
  
  /** Combines two streams into one using cantor's unparining function.
    *  Ensures that the stream terminates if both streams terminate */
  def combine[A, B](sa: Stream[A], sb: Stream[B]): Stream[(A, B)] = {
    def combineRec[A, B](sa: Stream[A], sb: Stream[B])(i: Int): Stream[(A, B)] = {
      val (x, y) = reverseCantorPair(i)
      if(!sa.isDefinedAt(x) && !sb.isDefinedAt(y)) Stream.Empty
      else if(sa.isDefinedAt(x) && sb.isDefinedAt(y)) (sa(x), sb(y)) #:: combineRec(sa, sb)(i+1)
      else combineRec(sa, sb)(i+1)
    }
    combineRec(sa, sb)(0)
  }
  
  /** Combines an arbitrary number of streams together. */
  def combine[A](sa: Seq[Stream[A]]): Stream[Seq[A]] = {
    if(sa.length == 0) Stream(Seq()) else
    if(sa.length == 1) sa(0).map(k => Seq(k)) else
    if(sa.length == 2) combine(sa(0), sa(1)).map(k => Seq(k._1, k._2)) else // Optimization
      combine(combine(sa.take(sa.length / 2)), combine(sa.drop(sa.length / 2))).map(k => k._1 ++ k._2)
  }
}


/**
 * @author Mikael
 */
class JoinProgramSet(sets: Seq[ProgramSet], recombine: Seq[Expr] => Expr) extends ProgramSet {
  
  def programs: Stream[Expr] = JoinProgramSet.combine(sets.map(_.programs)).map(recombine)
}