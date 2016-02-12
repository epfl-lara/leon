/**
  * Name:     CustomRender.scala
  * Creation: 15.1.2015
  * Author:   Mikael Mayer (mikael.mayer@epfl.ch)
  * Comments: Custom generic rendering
  */

import leon.lang._
import leon.annotation._
import leon.collection._
import leon.collection.ListOps._
import leon.lang.synthesis._

object CustomRender {
  def generic_list[T](l: List[T], f: T => String): String = {
    ???
  } ensuring {
    (res: String) => ((l, res) passes {
      case Nil() => "[]"
      case Cons(a, Cons(b, Nil())) => "[" + f(a) + ", " + f(b) + "]"
    })
  }
}