/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

/* The calculus of Computation textbook */

object LinearSearch {

  def linearSearch(a: Array[Int], c: Int): Boolean = ({
    require(a.length >= 0)
    var i = 0
    var found = false
    (while(i < a.length) {
      if(a(i) == c)
        found = true
      i = i + 1
    }) invariant(
         i <= a.length &&
         i >= 0 &&
         (if(found) contains(a, i, c) else !contains(a, i, c))
       )
    found
  }) ensuring(res => if(res) contains(a, a.length, c) else !contains(a, a.length, c))

  def contains(a: Array[Int], size: Int, c: Int): Boolean = {
    require(a.length >= 0 && size >= 0 && size <= a.length)
    content(a, size).contains(c)
  }

  // Set not supported by GenC
  def content(a: Array[Int], size: Int): Set[Int] = {
    require(a.length >= 0 && size >= 0 && size <= a.length)
    var set = Set.empty[Int]
    var i = 0
    (while(i < size) {
      set = set ++ Set(a(i))
      i = i + 1
    }) invariant(i >= 0 && i <= size)
    set
  }

  def _main() = {
    val array = Array(55, 0, -5, 9, 13, 42, -27, 0)
    if (linearSearch(array, 42) && !linearSearch(array, 58)) 0
    else 1
  }

  @extern
  def main(args: Array[String]) = _main()

}
