package scala.collection.immutable


object Multiset {
   /** The empty set of this type */
  def empty[A]: Multiset[A] = new EmptyMultiset[A]
  
  /** The canonical factory for this type */
  def apply[A](elems: A*): Multiset[A] = empty[A] +++ elems
  
}

trait Multiset[A] extends AnyRef with collection.Multiset[A]{
  
  /** This method is an alias for <code>intersect</code>.
   *  It computes an intersection with multiset <code>that</code>.
   *  It removes all the elements that are not present in <code>that</code>.
   *
   *  @param that the multiset to intersect with
   */
  final override def ** (that: collection.Multiset[A]): Multiset[A] = intersect(that)

  /** 
   * This method computes an intersection with multiset that. It removes all 
   * the elements that are not present in that.
   */
  def intersect (that: collection.Multiset[A]): Multiset[A] 
  
  // A U elems (max)
  def ++ (elems: Iterable[A]): Multiset[A]
  
  // A U elems (sum)
  def +++ (elems: Iterable[A]): Multiset[A]
  
  // A \ {elems} 
  def --(elems: Iterable[A]): Multiset[A]
  
  // A U {elems}
  final def + (elems: A*): Multiset[A] = this ++ elems
  
  // A \ {elems}
  final def - (elems: A*): Multiset[A] = this -- elems
  
  def filter (p: A => Boolean): Iterable[A]
}
