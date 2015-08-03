/* Copyright 2009-2015 EPFL, Lausanne */

import leon.lang._
import leon.lang.xlang._

object Epsilon4 {

  sealed abstract class MyList
  case class MyCons(head: Int, tail: MyList) extends MyList
  case class MyNil() extends MyList

  def size(lst: MyList): Int = (lst match {
    case MyNil() => 0
    case MyCons(_, xs) => 1 + size(xs)
  })

  def toSet(lst: MyList): Set[Int] = lst match {
    case MyCons(x, xs) => toSet(xs) ++ Set(x)
    case MyNil() => Set[Int]()
  }

  def toList(set: Set[Int]): MyList = if(set == Set.empty[Int]) MyNil() else {
    val elem = epsilon((x : Int) => set contains x)
    MyCons(elem, toList(set -- Set[Int](elem)))
  }


  def wrongProperty0(lst: MyList): Boolean = (size(toList(toSet(lst))) == size(lst)).holds
  //def wrongProperty1(lst: MyList): Boolean = (toList(toSet(lst)) == lst).holds
}
