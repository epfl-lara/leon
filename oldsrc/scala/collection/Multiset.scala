package scala.collection


trait Multiset[A] extends (A => Int) with Collection[A]{
  
  /** Returns the number of elements in this multiset.
   *
   *  @return number of multiset elements.
   */
  def size: Int
  
  /** This method allows multisets to be interpreted as predicates.
   *  It returns <code>0</code>, iff this multiset does not contain 
   *  element <code>elem</code>, or <code>N</code> where <code>N</code>
   *  is the number of occurences of <code>elem</code> in this multiset.
   *
   *  @param elem the element to check for membership.
   *  @return     <code>0</code> iff <code>elem</code> is not contained in
   *              this multiset, or <code>N</code> where <code>N</code>
   *              is the number of occurences of <code>elem</code> in this 
   *              multiset.
   */
  def apply(elem: A): Int  
  
  /** Checks if this set contains element <code>elem</code>.
   *
   *  @param elem the element to check for membership.
   *  @return     <code>true</code> iff <code>elem</code> is not contained in
   *              this multiset.
   */
  def contains(elem: A): Boolean = apply(elem) > 0
  
  /** Checks if this multiset is empty.
   *
   *  @return <code>true</code> iff there is no element in the multiset.
   */
  override def isEmpty: Boolean = size == 0
  
  /** Checks if this multiset is a subset of set <code>that</code>.
   *
   *  @param that another multiset.
   *  @return     <code>true</code> iff the other multiset is a superset of
   *              this multiset.
   *  todo: rename to isSubsetOf 
   */
  def subsetOf(that: Multiset[A]): Boolean = 
    forall(e => this(e) <= that(e))
  
  /** 
   * This method is an alias for <code>intersect</code>. It computes an 
   * intersection with set that. It removes all the elements 
   * <code>that</code> are not present in that.
   */                                                    
  def ** (that: Multiset[A]): Multiset[A]
  
  /** @return this multiset as set. */
  def asSet: Set[A]
    
  
  //structural equality
  /** Compares this multiset with another object and returns true, iff the
   *  other object is also a multiset which contains the same elements as
   *  this multiset, with the same cardinality.
   *
   *  @param that the other object
   *  @note not necessarily run-time type safe.
   *  @return     <code>true</code> iff this multiset and the other multiset
   *              contain the same elements, with same cardinality.
   */
  override def equals(that: Any): Boolean = that match {
    case other: Multiset[_] => other.size == this.size && subsetOf(other.asInstanceOf[Multiset[A]])
    case _ => false
  }
  
  /** Defines the prefix of this object's <code>toString</code> representation.
   */
  override protected def stringPrefix : String = "Multiset"
  
  
  override def toString = elements.mkString(stringPrefix + "(", ", ", ")")
}
