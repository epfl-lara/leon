import scala.collection.immutable.Set
import funcheck.Annotations._
import funcheck.Utils._

import cp.Definitions._
import cp.Terms._

import scala.collection.immutable.{List=>SList}

@spec object Specs {
  sealed abstract class List
  case class Cons(head : Int, tail : List) extends List
  case class Nill() extends List

  def content(l : List) : Set[Int] = l match {
    case Nill() => Set.empty[Int]
    case Cons(x, xs) => Set(x) ++ content(xs)
  }

  def size(l : List) : Int = (l match {
    case Nill() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def isSorted(l : List) : Boolean = l match {
    case Nill() => true
    case Cons(_, Nill()) => true
    case Cons(x, xs @ Cons(y, ys)) => (x < y) && isSorted(xs)
  }
}

object SortedListMethods {
  import Specs._

  implicit def l2sl(l : List) : SList[Int] = l match {
    case Cons(x, xs) => x :: l2sl(xs)
    case Nill() => Nil
  }

  implicit def sl2l(l : SList[Int]) : List = l match {
    case Nil => Nill()
    case x :: xs => Cons(x, sl2l(xs))
  }

  def addDeclarative(x : Int, list : List) : List =
    ((l : List) => isSorted(l) && content(l) == content(list) ++ Set(x)).solve

  def removeDeclarative(x : Int, list : List) : List = 
    ((l : List) => isSorted(l) && content(l) == content(list) -- Set(x)).solve

  def randomList(size : Int, from : Int, to : Int) : List = {
    import scala.collection.mutable.{Set=>MSet}
    val nums = MSet.empty[Int]
    while(nums.size < size) {
      nums += scala.util.Random.nextInt(1 + to - from) + from
      nums -= 42
    }
    sl2l(nums.toList.sorted)
  }

  def printLists(lists : List*) : Unit = {
    println(lists.toList.map(l2sl).mkString("\n"))
  }

  def main(args : Array[String]) : Unit = {
    val listSize = if(args.isEmpty) 3 else args(0).toInt
    val nbLists = if(args.size <= 1) 5 else args(1).toInt

    val lists = for(i <- 1 to nbLists) yield randomList(listSize, -200, 200)

    println("Starting lists :")
    printLists(lists : _*)

    val beforeAdd = System.currentTimeMillis
    val listsWith42 = lists.map(addDeclarative(42, _))
    val afterAdd = System.currentTimeMillis

    println("Lists with 42 :")
    printLists(listsWith42 : _*)

    val beforeRemove = System.currentTimeMillis
    val listsWithout42 = listsWith42.map(removeDeclarative(42, _))
    val afterRemove = System.currentTimeMillis

    println("Lists without 42 :")
    printLists(listsWithout42 : _*)

    println("List size : " + listSize + " (running on " + nbLists + " lists)")
    val addTime = (afterAdd - beforeAdd).toDouble / (nbLists * 1000.0d)
    val remTime = (afterRemove - beforeRemove).toDouble / (nbLists * 1000.0d)
    println("Adding took   (on avg.) : " + addTime + " seconds.")
    println("Removing took (on avg.) : " + remTime + " seconds.")

    // LaTeX-friendly line
    println("%2d & %1.2f & %1.2f".format(listSize, addTime, remTime))

  }
}
