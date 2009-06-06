package scala.collection.immutable

class EmptyMultiset[A] extends Multiset[A] with Helper[A]{

  def empty[C]: Multiset[C] = new EmptyMultiset[C]
  
  override def size: Int = 0
  
  override def apply(elem: A): Int = 0
  
  override def contains(elem: A): Boolean = false

  override def intersect (that: collection.Multiset[A]): Multiset[A] = empty
  
  override def ++ (elems: Iterable[A]): Multiset[A] = iterable2multiset(elems)
  
  override def +++ (elems: Iterable[A]): Multiset[A] = this ++ elems
  
  override def --(elems: Iterable[A]): Multiset[A] = empty
  
  override def elements: Iterator[A] = Iterator.empty
}
