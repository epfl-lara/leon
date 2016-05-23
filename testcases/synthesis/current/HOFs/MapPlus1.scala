import leon.lang._
import leon.lang.synthesis._


object MapPlus1 {
  abstract class List
  case object Nil extends List
  case class Cons(h: BigInt, t: List) extends List

  def size(l: List): BigInt = {
    l match {
      case Cons(h, t) =>  size(t) + 1
      case Nil => BigInt(0)
    }
  } ensuring { res => res >= 0 }

  def sum(l: List): BigInt = {
    l match {
      case Cons(h, t) =>  h + sum(t)
      case Nil => BigInt(0)
    }
  }


  def map(l: List, f: BigInt => BigInt): List = {
    l match {
      case Nil => Nil
      case Cons(h, t) => Cons(f(h), map(t, f))
    }
  } ensuring { res =>
    size(res) == size(l)
  }


  def test(l: List): List = {
      ???[List]
  } ensuring { res =>
    (sum(res) == sum(l) + size(l)) &&
    (size(res) == size(l))
  }

}
