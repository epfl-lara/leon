import leon.lang._
import leon.collection._

object Sets1 {
  def set(i: Int): Int => Boolean = x => x == i

  def complement(s: Int => Boolean): Int => Boolean = x => !s(x)

  def union(s1: Int => Boolean, s2: Int => Boolean): Int => Boolean = x => s1(x) || s2(x)

  def intersection(s1: Int => Boolean, s2: Int => Boolean): Int => Boolean = x => s1(x) && s2(x)

  def failing(s1: Int => Boolean, s2: Int => Boolean): Boolean = {
    complement(intersection(union(s1, s2), s1)) == s2
  }.holds

}
