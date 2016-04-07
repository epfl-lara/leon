/* Copyright 2009-2016 EPFL, Lausanne */

package leon.theories
import leon.lang.forall
import leon.annotation._

@library
sealed case class Bag[T](f: T => BigInt) {
  def get(x: T): BigInt = f(x)
  def add(elem: T): Bag[T] = Bag((x: T) => f(x) + (if (x == elem) 1 else 0))
  def union(that: Bag[T]): Bag[T] = Bag((x: T) => f(x) + that.f(x))
  def difference(that: Bag[T]): Bag[T] = Bag((x: T) => {
    val res = f(x) - that.f(x)
    if (res < 0) 0 else res
  })

  def intersect(that: Bag[T]): Bag[T] = Bag((x: T) => {
    val r1 = f(x)
    val r2 = that.f(x)
    if (r1 > r2) r2 else r1
  })

  def equals(that: Bag[T]): Boolean = forall((x: T) => f(x) == that.f(x))
}
