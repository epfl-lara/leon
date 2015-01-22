/* Copyright 2009-2014 EPFL, Lausanne */

package leon.custom

import leon._
import leon.lang._
import leon.annotation._

sealed abstract class List0[T] {
  def size: Int = (this match {
    case Nil0() => 0
    case Cons0(h, t) => 1 + t.size
  }) ensuring (_ >= 0)

  def content: Set[T] = this match {
    case Nil0() => Set()
    case Cons0(h, t) => Set(h) ++ t.content
  }

  def contains(v: T): Boolean = (this match {
    case Cons0(h, t) if h == v => true
    case Cons0(_, t) => t.contains(v)
    case Nil0() => false
  }) ensuring { res => res == (content contains v) }

  def ++(that: List0[T]): List0[T] = (this match {
    case Nil0() => that
    case Cons0(x, xs) => Cons0(x, xs ++ that)
  }) ensuring { res => (res.content == this.content ++ that.content) && (res.size == this.size + that.size)}

  def head: T = {
    require(this != Nil0[T]())
    this match {
      case Cons0(h, t) => h
    }
  }

  def tail: List0[T] = {
    require(this != Nil0[T]())
    this match {
      case Cons0(h, t) => t
    }
  }

  def apply(index: Int): T = {
    require(0 <= index && index < size)
    if (index == 0) {
      head
    } else {
       tail(index-1)
    }
  }

  def ::(t:T): List0[T] = Cons0(t, this)

  def :+(t:T): List0[T] = {
    this match {
      case Nil0() => Cons0(t, this)
      case Cons0(x, xs) => Cons0(x, xs :+ (t))
    }
  } ensuring(res => (res.size == size + 1) && (res.content == content ++ Set(t)))

  def reverse: List0[T] = {
    this match {
      case Nil0() => this
      case Cons0(x,xs) => xs.reverse :+ x
    }
  } ensuring (res => (res.size == size) && (res.content == content))

  def take(i: Int): List0[T] = (this, i) match {
    case (Nil0(), _) => Nil0()
    case (Cons0(h, t), i) =>
      if (i == 0) {
        Nil0()
      } else {
        Cons0(h, t.take(i-1))
      }
  }

  def drop(i: Int): List0[T] = (this, i) match {
    case (Nil0(), _) => Nil0()
    case (Cons0(h, t), i) =>
      if (i == 0) {
        Cons0(h, t)
      } else {
        t.drop(i-1)
      }
  }

  def slice(from: Int, to: Int): List0[T] = {
    require(from < to && to < size && from >= 0)
    drop(from).take(to-from)
  }

  def replace(from: T, to: T): List0[T] = this match {
    case Nil0() => Nil0()
    case Cons0(h, t) =>
      val r = t.replace(from, to)
      if (h == from) {
        Cons0(to, r)
      } else {
        Cons0(h, r)
      }
  }

  private def chunk0(s: Int, l: List0[T], acc: List0[T], res: List0[List0[T]], s0: Int): List0[List0[T]] = l match {
    case Nil0() =>
      if (acc.size > 0) {
        res :+ acc
      } else {
        res
      }
    case Cons0(h, t) =>
      if (s0 == 0) {
        chunk0(s, l, Nil0(), res :+ acc, s)
      } else {
        chunk0(s, t, acc :+ h, res, s0-1)
      }
  }

  def chunks(s: Int): List0[List0[T]] = {
    require(s > 0)

    chunk0(s, this, Nil0(), Nil0(), s)
  }

  def zip[B](that: List0[B]): List0[(T, B)] = (this, that) match {
    case (Cons0(h1, t1), Cons0(h2, t2)) =>
      Cons0((h1, h2), t1.zip(t2))
    case (_) =>
      Nil0()
  }

  def -(e: T): List0[T] = this match {
    case Cons0(h, t) =>
      if (e == h) {
        t - e
      } else {
        Cons0(h, t - e)
      }
    case Nil0() =>
      Nil0()
  }

  def --(that: List0[T]): List0[T] = this match {
    case Cons0(h, t) =>
      if (that.contains(h)) {
        t -- that
      } else {
        Cons0(h, t -- that)
      }
    case Nil0() =>
      Nil0()
  }

  def &(that: List0[T]): List0[T] = this match {
    case Cons0(h, t) =>
      if (that.contains(h)) {
        Cons0(h, t & that)
      } else {
        t & that
      }
    case Nil0() =>
      Nil0()
  }

  def pad(s: Int, e: T): List0[T] = { (this, s) match {
    case (_, s) if s <= 0 =>
      this
    case (Nil0(), s) =>
      Cons0(e, Nil0().pad(s-1, e))
    case (Cons0(h, t), s) =>
      Cons0(h, t.pad(s-1, e)) // FIXME should be s
  }} ensuring { res =>
    ((this,s,e), res) passes {
      case (Cons0(a,Nil0()), 2, x) => Cons0(a, Cons0(x, Cons0(x, Nil0())))
    }
  }

  def find(e: T): Option[Int] = this match {
    case Nil0() => None()
    case Cons0(h, t) =>
      if (h == e) {
        Some(0)
      } else {
        t.find(e) match {
          case None()  => None()
          case Some(i) => Some(i+1)
        }
      }
  }

  def init: List0[T] = (this match {
    case Cons0(h, Nil0()) =>
      Nil0[T]()
    case Cons0(h, t) =>
      Cons0[T](h, t.init)
    case Nil0() =>
      Nil0[T]()
  }) ensuring ( (r: List0[T]) => ((r.size < this.size) || (this.size == 0)) )

  def lastOption: Option[T] = this match {
    case Cons0(h, t) =>
      t.lastOption.orElse(Some(h))
    case Nil0() =>
      None()
  }

  def firstOption: Option[T] = this match {
    case Cons0(h, t) =>
      Some(h)
    case Nil0() =>
      None()
  }

  def unique: List0[T] = this match {
    case Nil0() => Nil0()
    case Cons0(h, t) =>
      Cons0(h, t.unique - h)
  }

  def splitAt(e: T): List0[List0[T]] =  split(Cons0(e, Nil0()))

  def split(seps: List0[T]): List0[List0[T]] = this match {
    case Cons0(h, t) =>
      if (seps.contains(h)) {
        Cons0(Nil0(), t.split(seps))
      } else {
        val r = t.split(seps)
        Cons0(Cons0(h, r.head), r.tail)
      }
    case Nil0() =>
      Cons0(Nil0(), Nil0())
  }

  def count(e: T): Int = this match {
    case Cons0(h, t) =>
      if (h == e) {
        1 + t.count(e)
      } else {
        t.count(e)
      }
    case Nil0() =>
      0
  }

  def evenSplit: (List0[T], List0[T]) = {
    val c = size/2
    (take(c), drop(c))
  }

  def insertAt(pos: Int, l: List0[T]): List0[T] = {
    if(pos < 0) {
      insertAt(size + pos, l)
    } else if(pos == 0) {
      l ++ this
    } else {
      this match {
        case Cons0(h, t) =>
          Cons0(h, t.insertAt(pos-1, l))
        case Nil0() =>
          l
      }
    }
  }

  def replaceAt(pos: Int, l: List0[T]): List0[T] = {
    if(pos < 0) {
      replaceAt(size + pos, l)
    } else if(pos == 0) {
      l ++ this.drop(l.size)
    } else {
      this match {
        case Cons0(h, t) =>
          Cons0(h, t.replaceAt(pos-1, l))
        case Nil0() =>
          l
      }
    }
  }

  def rotate(s: Int): List0[T] = {
    if (s < 0) {
      rotate(size+s)
    } else {
      val s2 = s % size
      drop(s2) ++ take(s2)
    }
  }

  def isEmpty = this match { 
    case Nil0() => true
    case _ => false 
  }

}

@ignore
object List0 {
  def apply[T](elems: T*): List0[T] = ???
}

@library
object List0Ops {
  def flatten[T](ls: List0[List0[T]]): List0[T] = ls match {
    case Cons0(h, t) => h ++ flatten(t)
    case Nil0() => Nil0()
  }

  def isSorted(ls: List0[Int]): Boolean = ls match {
    case Nil0() => true
    case Cons0(_, Nil0()) => true
    case Cons0(h1, Cons0(h2, _)) if(h1 > h2) => false
    case Cons0(_, t) => isSorted(t)
  }

  def sorted(ls: List0[Int]): List0[Int] = ls match {
    case Cons0(h, t) => insSort(sorted(t), h)
    case Nil0() => Nil0()
  }

  def insSort(ls: List0[Int], v: Int): List0[Int] = ls match {
    case Nil0() => Cons0(v, Nil0())
    case Cons0(h, t) =>
      if (v <= h) {
        Cons0(v, t)
      } else {
        Cons0(h, insSort(t, v))
      }
  }
}


case class Cons0[T](h: T, t: List0[T]) extends List0[T]
case class Nil0[T]() extends List0[T]

@library
object List0Specs {
  def snocIndex[T](l : List0[T], t : T, i : Int) : Boolean = {
    require(0 <= i && i < l.size + 1)
    // proof:
    (l match {
      case Nil0() => true
      case Cons0(x, xs) => if (i > 0) snocIndex[T](xs, t, i-1) else true
    }) &&
    // claim:
    ((l :+ t).apply(i) == (if (i < l.size) l(i) else t))
  }.holds

  def reverseIndex[T](l : List0[T], i : Int) : Boolean = {
    require(0 <= i && i < l.size)
    (l match {
      case Nil0() => true
      case Cons0(x,xs) => snocIndex(l, x, i) && reverseIndex[T](l,i)
    }) &&
    (l.reverse.apply(i) == l.apply(l.size - 1 - i))
  }.holds

  def appendIndex[T](l1 : List0[T], l2 : List0[T], i : Int) : Boolean = {
    require(0 <= i && i < l1.size + l2.size)
    (l1 match {
      case Nil0() => true
      case Cons0(x,xs) => if (i==0) true else appendIndex[T](xs,l2,i-1)
    }) &&
    ((l1 ++ l2).apply(i) == (if (i < l1.size) l1(i) else l2(i - l1.size)))
  }.holds

  def appendAssoc[T](l1 : List0[T], l2 : List0[T], l3 : List0[T]) : Boolean = {
    (l1 match {
      case Nil0() => true
      case Cons0(x,xs) => appendAssoc(xs,l2,l3)
    }) &&
    (((l1 ++ l2) ++ l3) == (l1 ++ (l2 ++ l3)))
  }.holds

  def snocIsAppend[T](l : List0[T], t : T) : Boolean = {
    (l match {
      case Nil0() => true
      case Cons0(x,xs) =>  snocIsAppend(xs,t)
    }) &&
    ((l :+ t) == l ++ Cons0[T](t, Nil0()))
  }.holds

  def snocAfterAppend[T](l1 : List0[T], l2 : List0[T], t : T) : Boolean = {
    (l1 match {
      case Nil0() => true
      case Cons0(x,xs) =>  snocAfterAppend(xs,l2,t)
    }) &&
    ((l1 ++ l2) :+ t == (l1 ++ (l2 :+ t)))
  }.holds

  def snocReverse[T](l : List0[T], t : T) : Boolean = {
    (l match {
      case Nil0() => true
      case Cons0(x,xs) => snocReverse(xs,t)
    }) &&
    ((l :+ t).reverse == Cons0(t, l.reverse))
  }.holds

  def reverseReverse[T](l : List0[T]) : Boolean = {
    (l match {
      case Nil0() => true
      case Cons0(x,xs) => reverseReverse[T](xs) && snocReverse[T](xs.reverse, x)
    }) &&
    (l.reverse.reverse == l)
  }.holds

  //// my hand calculation shows this should work, but it does not seem to be found
  //def reverseAppend[T](l1 : List0[T], l2 : List0[T]) : Boolean = {
  //  (l1 match {
  //    case Nil0() => true
  //    case Cons0(x,xs) => {
  //      reverseAppend(xs,l2) &&
  //      snocAfterAppend[T](l2.reverse, xs.reverse, x) &&
  //      l1.reverse == (xs.reverse :+ x)
  //    }
  //  }) &&
  //  ((l1 ++ l2).reverse == (l2.reverse ++ l1.reverse))
  //}.holds
}
