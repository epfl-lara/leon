package scala.collection.immutable


object MultiSet {
   /** The empty set of this type */
  def empty[A]: MultiSet[A] = throw new UnsupportedOperationException("Concrete MultiSet classes need to be implemented")
  
  /** The canonical factory for this type */
  def apply[A](elems: A*): MultiSet[A] = empty[A] ++ elems
  
}

trait MultiSet[A] extends AnyRef with collection.MultiSet[A]{
  
  /** This method is an alias for <code>intersect</code>.
   *  It computes an intersection with multiset <code>that</code>.
   *  It removes all the elements that are not present in <code>that</code>.
   *
   *  @param that the multiset to intersect with
   */
  override def ** (that: collection.MultiSet[A]): MultiSet[A] = intersect(that)

  /** 
   * This method computes an intersection with multiset that. It removes all 
   * the elements that are not present in that.
   */
  def intersect (that: collection.MultiSet[A]): MultiSet[A] 
  
  // A U elems (max)
  def ++ (elems: Iterable[A]): MultiSet[A]
  
  // A U elems (sum)
  def +++ (elems: Iterable[A]): MultiSet[A]
  
  // A \ {elems} 
  def --(elems: Iterable[A]): MultiSet[A]
  
  // A U {elems}
  def + (elems: A*): MultiSet[A] 
  
  // A \ {elems}
  def - (elems: A*): MultiSet[A] 
  
  def filter (p: A => Boolean): Iterable[A]
}
