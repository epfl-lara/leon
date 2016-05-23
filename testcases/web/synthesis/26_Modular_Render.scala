/** 
  * Name:     ModularRender.scala
  * Creation: 26.01.2015
  * Author:   Mikael Mayer (mikael.mayer@epfl.ch)
  * Comments: Modular rendering, in one order or the other.
  */
import leon.lang._
import leon.annotation._
import leon.collection._
import leon.collection.ListOps._
import leon.lang.synthesis._

object ModularRender {
  
  def booleanToString(b: Boolean) = if(b) "Up" else "Down"

  def intToString(b: BigInt) = b.toString
  
  def customToString[T](l : List[T], f : (T) => String): String =
    ???[String] ask l
  
  case class Configuration(flags: List[Boolean], strokes: List[BigInt])

  // We want to write
  // Solution:
  //   [Up, Down,  Up....]
  //   [1, 2, 5, ...]
  def ConfigToString(config : Configuration): String =
    ???[String] ask config
  
  /** Wrong lemma for demonstration */
  def configurationsAreSimple(c: Configuration) =
    (c.flags.size < 3 || c.strokes.size < 2 || c.flags(0) == c.flags(1) || c.strokes(0) == c.strokes(1)) holds
}
