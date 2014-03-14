/* Copyright 2009-2014 EPFL, Lausanne */

package leon.collection

import leon.lang._
import leon.annotation._

sealed abstract class List[T] {
  @verified
  def size: Int = (this match {
    case Nil() => 0
    case Cons(h, t) => 1 + t.size
  }) ensuring (_ >= 0)

  @verified
  def content: Set[T] = this match {
    case Nil() => Set()
    case Cons(h, t) => Set(h) ++ t.content
  }

  @verified
  def contains(v: T): Boolean = (this match {
    case Cons(h, t) if h == v => true
    case Cons(_, t) => t.contains(v)
    case Nil() => false
  }) ensuring { res => res == (content contains v) }

  @verified
  def ++(that: List[T]): List[T] = (this match {
    case Nil() => that
    case Cons(x, xs) => Cons(x, xs ++ that)
  }) ensuring { res => (res.content == this.content ++ that.content) && (res.size == this.size + that.size)}

  @verified
  def head: T = {
    require(this != Nil[T]())
    this match {
      case Cons(h, t) => h
    }
  }

  @verified
  def tail: List[T] = {
    require(this != Nil[T]())
    this match {
      case Cons(h, t) => t
    }
  }

  @verified
  def apply(index: Int): T = {
    require(0 <= index && index < size)
    if (index == 0) {
      head
    } else {
       tail(index-1)
    }
  }

  @verified
  def :+(t:T): List[T] = {
    this match {
      case Nil() => Cons(t, this)
      case Cons(x, xs) => Cons(x, xs :+ (t))
    }
  } ensuring(res => (res.size == size + 1) && (res.content == content ++ Set(t)))

  @verified
  def reverse: List[T] = {
    this match {
      case Nil() => this
      case Cons(x,xs) => xs.reverse :+ x
    }
  } ensuring (res => (res.size == size) && (res.content == content))
}


case class Cons[T](h: T, t: List[T]) extends List[T]
case class Nil[T]() extends List[T]

object ListSpecs {
  @verified
  def snocIndex[T](l : List[T], t : T, i : Int) : Boolean = {
    require(0 <= i && i < l.size + 1)
    // proof:
    (l match {
      case Nil() => true
      case Cons(x, xs) => if (i > 0) snocIndex[T](xs, t, i-1) else true
    }) &&
    // claim:
    ((l :+ t).apply(i) == (if (i < l.size) l(i) else t))
  }.holds

  @verified
  def reverseIndex[T](l : List[T], i : Int) : Boolean = {
    require(0 <= i && i < l.size)
    (l match {
      case Nil() => true
      case Cons(x,xs) => snocIndex(l, x, i) && reverseIndex[T](l,i)
    }) &&
    (l.reverse.apply(i) == l.apply(l.size - 1 - i))
  }.holds

  @verified
  def appendIndex[T](l1 : List[T], l2 : List[T], i : Int) : Boolean = {
    require(0 <= i && i < l1.size + l2.size)
    (l1 match {
      case Nil() => true
      case Cons(x,xs) => if (i==0) true else appendIndex[T](xs,l2,i-1)
    }) &&
    ((l1 ++ l2).apply(i) == (if (i < l1.size) l1(i) else l2(i - l1.size)))
  }.holds

  @verified
  def appendAssoc[T](l1 : List[T], l2 : List[T], l3 : List[T]) : Boolean = {
    (l1 match {
      case Nil() => true
      case Cons(x,xs) => appendAssoc(xs,l2,l3)
    }) &&
    (((l1 ++ l2) ++ l3) == (l1 ++ (l2 ++ l3)))
  }.holds

  @verified
  def snocIsAppend[T](l : List[T], t : T) : Boolean = {
    (l match {
      case Nil() => true
      case Cons(x,xs) =>  snocIsAppend(xs,t)
    }) &&
    ((l :+ t) == l ++ Cons[T](t, Nil()))
  }.holds

  @verified
  def snocAfterAppend[T](l1 : List[T], l2 : List[T], t : T) : Boolean = {
    (l1 match {
      case Nil() => true
      case Cons(x,xs) =>  snocAfterAppend(xs,l2,t)
    }) &&
    ((l1 ++ l2) :+ t == (l1 ++ (l2 :+ t)))
  }.holds

  @verified
  def snocReverse[T](l : List[T], t : T) : Boolean = {
    (l match {
      case Nil() => true
      case Cons(x,xs) => snocReverse(xs,t)
    }) &&
    ((l :+ t).reverse == Cons(t, l.reverse))
  }.holds

  @verified
  def reverseReverse[T](l : List[T]) : Boolean = {
    (l match {
      case Nil() => true
      case Cons(x,xs) => reverseReverse[T](xs) && snocReverse[T](xs.reverse, x)
    }) &&
    (l.reverse.reverse == l)
  }.holds

  //// my hand calculation shows this should work, but it does not seem to be found
  //def reverseAppend[T](l1 : List[T], l2 : List[T]) : Boolean = {
  //  (l1 match {
  //    case Nil() => true
  //    case Cons(x,xs) => {
  //      reverseAppend(xs,l2) &&
  //      snocAfterAppend[T](l2.reverse, xs.reverse, x) &&
  //      l1.reverse == (xs.reverse :+ x)
  //    }
  //  }) &&
  //  ((l1 ++ l2).reverse == (l2.reverse ++ l1.reverse))
  //}.holds
}
