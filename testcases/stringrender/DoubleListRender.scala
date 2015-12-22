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

  def mutual_lists(a : A): String =  {
    ???
  } ensuring {
    (res : String) => (a, res) passes {
      case N() =>
        "[]"
      case B(NN(), N()) =>
        "[()]"
      case B(NN(), B(NN(), N())) =>
        "[(), ()]"
      case B(BB(N(), NN()), N()) =>
        "[([])]"
      case B(NN(), B(NN(), B(NN(), N()))) =>
        "[(), (), ()]"
      case B(BB(N(), BB(N(), NN())), N()) =>
        "[([], [])]"
      case B(NN(), B(BB(N(), NN()), N())) =>
        "[(), ([])]"
      case B(BB(N(), NN()), B(NN(), N())) =>
        "[([]), ()]"
      case B(BB(B(NN(), N()), NN()), N()) =>
        "[([()])]"
      case B(BB(N(), BB(N(), BB(N(), NN()))), N()) =>
        "[([], [], [])]"
      case B(NN(), B(BB(N(), NN()), B(NN(), N()))) =>
        "[(), ([]), ()]"
      case B(BB(B(NN(), N()), BB(N(), NN())), N()) =>
        "[([()], [])]"
      case B(BB(B(BB(N(), NN()), N()), NN()), N()) =>
        "[([([])])]"
      case B(BB(B(NN(), B(NN(), N())), NN()), N()) =>
        "[([(), ()])]"
      case B(BB(N(), BB(B(NN(), N()), NN())), N()) =>
        "[([], [()])]"
    }
  }
}