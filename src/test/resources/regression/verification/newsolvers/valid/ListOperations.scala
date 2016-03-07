/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._
import leon.collection._

object ListOperations {

  def size[A](l: List[A]) : BigInt = (l match {
    case Nil() => BigInt(0)
    case Cons(_, t) => BigInt(1) + size(t)
  }) ensuring(res => res >= 0)

  def content[A](l: List[A]) : Set[A] = l match {
    case Nil() => Set[A]()
    case Cons(h, t) => content(t) ++ Set[A](h)
  }

  def zip[A,B](l1: List[A], l2: List[B]): List[(A, B)] = {
    // try to comment this and see how pattern-matching becomes
    // non-exhaustive and post-condition fails
    require(size(l1) == size(l2))
    (l1, l2) match {
      case (Nil(), Nil()) => 
        Nil[(A, B)]()
      case (Cons(x, xs), Cons(y, ys)) => 
        Cons( (x,y), zip(xs, ys) )
    }
  } ensuring(size(_) == size(l1))

  def sizeTailRec[A](l: List[A]) : BigInt = sizeTailRecAcc(l, 0)

  def sizeTailRecAcc[A](l: List[A], acc: BigInt) : BigInt = {
   require(acc >= 0)
   l match {
     case Nil() => acc
     case Cons(_, xs) => sizeTailRecAcc(xs, acc+1)
   }
  } ensuring(res => res == size(l) + acc)

  def sizesAreEquiv[A](l: List[A]) : Boolean = {
    size(l) == sizeTailRec(l)
  }.holds

  def sizeAndContent[A](l: List[A]) : Boolean = {
    size(l) == BigInt(0) || content(l) != Set.empty[A]
  }.holds
  
  def drunk[A](l : List[A]) : List[A] = (l match {
    case Nil() => Nil[A]()
    case Cons(x,l1) => Cons(x,Cons(x,drunk(l1)))
  }) ensuring (size(_) == 2 * size(l))

  def reverse[A](l: List[A]) : List[A] = reverse0(l, Nil[A]()) ensuring(content(_) == content(l))
  def reverse0[A](l1: List[A], l2: List[A]) : List[A] = (l1 match {
    case Nil() => l2
    case Cons(x, xs) => reverse0(xs, Cons[A](x, l2))
  }) ensuring(content(_) == content(l1) ++ content(l2))

  def append[A](l1 : List[A], l2 : List[A]) : List[A] = (l1 match {
    case Nil() => l2
    case Cons(x,xs) => Cons[A](x, append(xs, l2))
  }) ensuring(content(_) == content(l1) ++ content(l2))

  @induct
  def nilAppend[A](l : List[A]) : Boolean = (append(l, Nil[A]()) == l).holds

  @induct
  def appendAssoc[A](xs : List[A], ys : List[A], zs : List[A]) : Boolean =
    (append(append(xs, ys), zs) == append(xs, append(ys, zs))).holds

  @induct
  def sizeAppend[A](l1 : List[A], l2 : List[A]) : Boolean =
    (size(append(l1, l2)) == size(l1) + size(l2)).holds

  @induct
  def concat[A](l1: List[A], l2: List[A]) : List[A] = 
    concat0(l1, l2, Nil[A]()) ensuring(content(_) == content(l1) ++ content(l2))

  @induct
  def concat0[A](l1: List[A], l2: List[A], l3: List[A]) : List[A] = (l1 match {
    case Nil() => l2 match {
      case Nil() => reverse(l3)
      case Cons(y, ys) => {
        concat0(Nil[A](), ys, Cons(y, l3))
      }
    }
    case Cons(x, xs) => concat0(xs, l2, Cons(x, l3))
  }) ensuring(content(_) == content(l1) ++ content(l2) ++ content(l3))
}
