/**
  * Name:     DoubleListRender.scala
  * Creation: 09.12.2015
  * Author:   Mikael Mayer (mikael.mayer@epfl.ch)
  * Comments: Double lists rendering specification (requires many disambiguation rounds)
  */
import leon.lang._
import leon.annotation._
import leon.collection._
import leon.collection.ListOps._
import leon.lang.synthesis._

object DoubleListRender {
  abstract class A
  case class B(i: AA, a: A) extends A
  case class N() extends A
  
  abstract class AA
  case class BB(i: A, a: AA) extends AA
  case class NN() extends AA
  
  // Obviously wrong, but it is useful to use the display function.
  def twoOutOfThreeAsAreTheSame(a: A, b: A, c: A): Boolean = {
    a == b || a == c || b == c
  } holds

  def AtoString(a : A): String =  {
    ???
  } ensuring {
    (res : String) => (a, res) passes {
      case B(BB(N(), BB(B(NN(), B(NN(), N())), NN())), N()) =>
        "[([], [(), ()])]"
    }
  }
}