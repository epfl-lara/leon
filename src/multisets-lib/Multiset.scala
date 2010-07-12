package scala.collection.immutable

case class UnimplementedFeatureException() extends Exception

object Multiset {
  def empty[A] : Multiset[A] = throw UnimplementedFeatureException()
  def apply[A](elems: A*) : Multiset[A] = throw UnimplementedFeatureException()
}

trait Multiset[A] {
  def ** (that: Multiset[A]) : Multiset[A] = throw UnimplementedFeatureException()
  def ++ (that: Multiset[A]) : Multiset[A] = throw UnimplementedFeatureException()
  def +++ (that: Multiset[A]) : Multiset[A] = throw UnimplementedFeatureException()
  def -- (that: Multiset[A]) : Multiset[A] = throw UnimplementedFeatureException()
  def toSet : scala.collection.immutable.Set[A] = throw UnimplementedFeatureException()
  def size : Int = throw UnimplementedFeatureException()
}
