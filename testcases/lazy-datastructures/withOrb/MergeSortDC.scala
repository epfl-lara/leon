package withOrb

import leon._
import lang._
import annotation._
import instrumentation._
import invariant._
import leon.collection._
import mem._
import higherorder._

object MergeSort {
  def log(n: BigInt): BigInt = {
    require(n >= 1)
    n match {
      case BigInt(1) => BigInt(0)
      case _ => log(n/2) + log(n - n/2)
    }
  }

  sealed abstract class List 
  case class Cons(head: BigInt, tail:List) extends List
  case class Nil() extends List

  def size(l: List): BigInt = {
    l match {
      case Nil() => BigInt(0)
      case Cons(_, xs) => 1 + size(xs)
    }
  } ensuring(res => res >= 0)

  def take(n: BigInt, l: List): List = {
    require(n >= 0 && size(l) >= n)
    n match {
      case BigInt(0) => Nil()
      case _ => l match {
        case Cons(x, xs) => Cons(x, take(n - 1, xs))
      }
    }
  } ensuring(res => (size(res) == n) && time <= ? * n + ?)

  def drop(n: BigInt, l: List): List = {
    require(n >= 0 && size(l) >= n)
    n match {
      case BigInt(0) => l
      case _ => l match {
        case Cons(x, xs) => drop(n - 1, xs)
      }
    }
  } ensuring(res => (size(res) == size(l) - n) && time <= ? * n + ?)

  def merge(x: List, y: List): List = {
    x match {
      case Nil() => y
      case Cons(xe, xs) => y match {
        case Nil() => x
        case Cons(ye, ys) => {
          if(xe <= ye) Cons(xe, Cons(ye, merge(xs, ys))) else Cons(ye, Cons(xe, merge(xs, ys)))
        }
      }
    }
  } ensuring(res => (size(res) == size(x) + size(y)) && time <= ? * size(x) + ? * size(y) + ?)

  def firsthalf(l: List): List = {
    val s = size(l)/2
    take(s, l)
  } ensuring(res => (size(res) == size(l)/2) && (time <= ? * (size(l)/2) + ?))

  // def mergesort(l: List): List = {
  //   merge(mergesort(take(size(l)/2, l)), mergesort(drop(size(l)/2, l)))
  // } ensuring(res => (size(res) == size(l)) && time <= ? * (size(l) * (size(l))) + ?)

}
