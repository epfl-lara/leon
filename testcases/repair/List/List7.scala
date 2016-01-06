/* Copyright 2009-2015 EPFL, Lausanne */

package leon.custom

import leon._
import leon.lang._
import leon.collection._
import leon.annotation._

sealed abstract class List[T] {
  def size: BigInt = (this match {
    case Nil() => BigInt(0)
    case Cons(h, t) => BigInt(1) + t.size
  }) ensuring (_ >= 0)

  def content: Set[T] = this match {
    case Nil() => Set()
    case Cons(h, t) => Set(h) ++ t.content
  }

  def contains(v: T): Boolean = (this match {
    case Cons(h, t) if h == v => true
    case Cons(_, t) => t.contains(v)
    case Nil() => false
  }) ensuring { res => res == (content contains v) }

  def ++(that: List[T]): List[T] = (this match {
    case Nil() => that
    case Cons(x, xs) => Cons(x, xs ++ that)
  }) ensuring { res => (res.content == this.content ++ that.content) && (res.size == this.size + that.size)}

  def head: T = {
    require(this != Nil[T]())
    this match {
      case Cons(h, t) => h
    }
  }

  def tail: List[T] = {
    require(this != Nil[T]())
    this match {
      case Cons(h, t) => t
    }
  }

  def apply(index: BigInt): T = {
    require(0 <= index && index < size)
    if (index == 0) {
      head
    } else {
       tail(index-1)
    }
  }

  def ::(t:T): List[T] = Cons(t, this)

  def :+(t:T): List[T] = {
    this match {
      case Nil() => Cons(t, this)
      case Cons(x, xs) => Cons(x, xs :+ (t))
    }
  } ensuring(res => (res.size == size + 1) && (res.content == content ++ Set(t)))

  def reverse: List[T] = {
    this match {
      case Nil() => this
      case Cons(x,xs) => xs.reverse :+ x
    }
  } ensuring (res => (res.size == size) && (res.content == content))

  def take(i: BigInt): List[T] = (this, i) match {
    case (Nil(), _) => Nil()
    case (Cons(h, t), i) =>
      if (i == 0) {
        Nil()
      } else {
        Cons(h, t.take(i-1))
      }
  }

  def drop(i: BigInt): List[T] = (this, i) match {
    case (Nil(), _) => Nil()
    case (Cons(h, t), i) =>
      if (i == 0) {
        Cons(h, t)
      } else {
        t.drop(i-1)
      }
  }

  def slice(from: BigInt, to: BigInt): List[T] = {
    require(from < to && to < size && from >= 0)
    drop(from).take(to-from)
  }

  def replace(from: T, to: T): List[T] = this match {
    case Nil() => Nil()
    case Cons(h, t) =>
      val r = t.replace(from, to)
      if (h == from) {
        Cons(to, r)
      } else {
        Cons(h, r)
      }
  }

  private def chunk0(s: BigInt, l: List[T], acc: List[T], res: List[List[T]], s0: BigInt): List[List[T]] = l match {
    case Nil() =>
      if (acc.size > 0) {
        res :+ acc
      } else {
        res
      }
    case Cons(h, t) =>
      if (s0 == 0) {
        chunk0(s, l, Nil(), res :+ acc, s)
      } else {
        chunk0(s, t, acc :+ h, res, s0-1)
      }
  }

  def chunks(s: BigInt): List[List[T]] = {
    require(s > 0)

    chunk0(s, this, Nil(), Nil(), s)
  }

  def zip[B](that: List[B]): List[(T, B)] = (this, that) match {
    case (Cons(h1, t1), Cons(h2, t2)) =>
      Cons((h1, h2), t1.zip(t2))
    case (_) =>
      Nil()
  }

  def -(e: T): List[T] = this match {
    case Cons(h, t) =>
      if (e == h) {
        t - e
      } else {
        Cons(h, t - e)
      }
    case Nil() =>
      Nil()
  }

  def --(that: List[T]): List[T] = this match {
    case Cons(h, t) =>
      if (that.contains(h)) {
        t -- that
      } else {
        Cons(h, t -- that)
      }
    case Nil() =>
      Nil()
  }

  def &(that: List[T]): List[T] = this match {
    case Cons(h, t) =>
      if (that.contains(h)) {
        Cons(h, t & that)
      } else {
        t & that
      }
    case Nil() =>
      Nil()
  }

  def pad(s: BigInt, e: T): List[T] = { (this, s) match {
    case (_, s) if s <= 0 =>
      this
    case (Nil(), s) =>
      Cons(e, Nil().pad(s-1, e))
    case (Cons(h, t), s) =>
      Cons(h, t.pad(s, e))
  }} ensuring { res =>
    ((this,s,e), res) passes {
      case (Cons(a,Nil()), BigInt(2), x) => Cons(a, Cons(x, Cons(x, Nil())))
    }
  }

  def find(e: T): Option[BigInt] = { this match {
    case Nil() => None[BigInt]()
    case Cons(h, t) =>
      if (h == e) {
        Some(BigInt(0))
      } else {
        t.find(e) match {
          case None()  => None[BigInt]()
          case Some(i) => Some(i) // FIXME forgot +1
        }
      }
  }} ensuring { res =>
    if (this.content contains e) {
      res.isDefined && this.size > res.get && this.apply(res.get) == e && res.get >= 0
    } else {
      res.isEmpty
    }
  }

  def init: List[T] = (this match {
    case Cons(h, Nil()) =>
      Nil[T]()
    case Cons(h, t) =>
      Cons[T](h, t.init)
    case Nil() =>
      Nil[T]()
  }) ensuring ( (r: List[T]) => ((r.size < this.size) || (this.size == 0)) )

  def lastOption: Option[T] = this match {
    case Cons(h, t) =>
      t.lastOption.orElse(Some(h))
    case Nil() =>
      None()
  }

  def firstOption: Option[T] = this match {
    case Cons(h, t) =>
      Some(h)
    case Nil() =>
      None()
  }

  def unique: List[T] = this match {
    case Nil() => Nil()
    case Cons(h, t) =>
      Cons(h, t.unique - h)
  }

  def splitAt(e: T): List[List[T]] =  split(Cons(e, Nil()))

  def split(seps: List[T]): List[List[T]] = this match {
    case Cons(h, t) =>
      if (seps.contains(h)) {
        Cons(Nil(), t.split(seps))
      } else {
        val r = t.split(seps)
        Cons(Cons(h, r.head), r.tail)
      }
    case Nil() =>
      Cons(Nil(), Nil())
  }

  def count(e: T): BigInt = this match {
    case Cons(h, t) =>
      if (h == e) {
        1 + t.count(e)
      } else {
        t.count(e)
      }
    case Nil() =>
      0
  }

  def evenSplit: (List[T], List[T]) = {
    val c = size/2
    (take(c), drop(c))
  }

  def insertAt(pos: BigInt, l: List[T]): List[T] = {
    if(pos < 0) {
      insertAt(size + pos, l)
    } else if(pos == 0) {
      l ++ this
    } else {
      this match {
        case Cons(h, t) =>
          Cons(h, t.insertAt(pos-1, l))
        case Nil() =>
          l
      }
    }
  }

  def replaceAt(pos: BigInt, l: List[T]): List[T] = {
    if(pos < 0) {
      replaceAt(size + pos, l)
    } else if(pos == 0) {
      l ++ this.drop(l.size)
    } else {
      this match {
        case Cons(h, t) =>
          Cons(h, t.replaceAt(pos-1, l))
        case Nil() =>
          l
      }
    }
  }

  def rotate(s: BigInt): List[T] = {
    if (s < 0) {
      rotate(size+s)
    } else {
      val s2 = s % size
      drop(s2) ++ take(s2)
    }
  }

  def isEmpty = this match { 
    case Nil() => true
    case _ => false 
  }

}

@ignore
object List {
  def apply[T](elems: T*): List[T] = ???
}

@library
object ListOps {
  def flatten[T](ls: List[List[T]]): List[T] = ls match {
    case Cons(h, t) => h ++ flatten(t)
    case Nil() => Nil()
  }

  def isSorted(ls: List[BigInt]): Boolean = ls match {
    case Nil() => true
    case Cons(_, Nil()) => true
    case Cons(h1, Cons(h2, _)) if(h1 > h2) => false
    case Cons(_, t) => isSorted(t)
  }

  def sorted(ls: List[BigInt]): List[BigInt] = ls match {
    case Cons(h, t) => insSort(sorted(t), h)
    case Nil() => Nil()
  }

  def insSort(ls: List[BigInt], v: BigInt): List[BigInt] = ls match {
    case Nil() => Cons(v, Nil())
    case Cons(h, t) =>
      if (v <= h) {
        Cons(v, t)
      } else {
        Cons(h, insSort(t, v))
      }
  }
}


case class Cons[T](h: T, t: List[T]) extends List[T]
case class Nil[T]() extends List[T]

@library
object ListSpecs {
  def snocIndex[T](l : List[T], t : T, i : BigInt) : Boolean = {
    require(0 <= i && i < l.size + 1)
    // proof:
    (l match {
      case Nil() => true
      case Cons(x, xs) => if (i > 0) snocIndex[T](xs, t, i-1) else true
    }) &&
    // claim:
    ((l :+ t).apply(i) == (if (i < l.size) l(i) else t))
  }.holds

  def reverseIndex[T](l : List[T], i : BigInt) : Boolean = {
    require(0 <= i && i < l.size)
    (l match {
      case Nil() => true
      case Cons(x,xs) => snocIndex(l, x, i) && reverseIndex[T](l,i)
    }) &&
    (l.reverse.apply(i) == l.apply(l.size - 1 - i))
  }.holds

  def appendIndex[T](l1 : List[T], l2 : List[T], i : BigInt) : Boolean = {
    require(0 <= i && i < l1.size + l2.size)
    (l1 match {
      case Nil() => true
      case Cons(x,xs) => if (i==0) true else appendIndex[T](xs,l2,i-1)
    }) &&
    ((l1 ++ l2).apply(i) == (if (i < l1.size) l1(i) else l2(i - l1.size)))
  }.holds

  def appendAssoc[T](l1 : List[T], l2 : List[T], l3 : List[T]) : Boolean = {
    (l1 match {
      case Nil() => true
      case Cons(x,xs) => appendAssoc(xs,l2,l3)
    }) &&
    (((l1 ++ l2) ++ l3) == (l1 ++ (l2 ++ l3)))
  }.holds

  def snocIsAppend[T](l : List[T], t : T) : Boolean = {
    (l match {
      case Nil() => true
      case Cons(x,xs) =>  snocIsAppend(xs,t)
    }) &&
    ((l :+ t) == l ++ Cons[T](t, Nil()))
  }.holds

  def snocAfterAppend[T](l1 : List[T], l2 : List[T], t : T) : Boolean = {
    (l1 match {
      case Nil() => true
      case Cons(x,xs) =>  snocAfterAppend(xs,l2,t)
    }) &&
    ((l1 ++ l2) :+ t == (l1 ++ (l2 :+ t)))
  }.holds

  def snocReverse[T](l : List[T], t : T) : Boolean = {
    (l match {
      case Nil() => true
      case Cons(x,xs) => snocReverse(xs,t)
    }) &&
    ((l :+ t).reverse == Cons(t, l.reverse))
  }.holds

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
