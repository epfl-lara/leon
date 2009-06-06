package scala.collection.immutable

object HashMultiset {
  
  /** The empty multiset of this type. */
  def empty[A] = new EmptyMultiset[A]
  
  /** The canonical factory for this type */
  def apply[A](elems: A*) = empty[A] ++ elems
}

class HashMultiset[A] private[immutable] (private val map: Map[A,Int]) extends Multiset[A] with Helper[A] {
  
  def empty[C]: Multiset[C] = new EmptyMultiset[C]
  
  override def size: Int = map.values.foldLeft(0)((a,b) => a+b)
  
  override def apply(elem: A): Int = map.getOrElse(elem,0)
    
  override def intersect (that: collection.Multiset[A]): Multiset[A] = {
    def inner(entries: List[A], result: Multiset[A]): Multiset[A] = entries match {
      case Nil => result
      case elem :: rest =>
        assert(!result.contains(elem))
        inner(rest, result ++ int2list(elem, min(this(elem),that(elem)))) 
    }
    
    inner(this.toList,empty)
  }
  
  
  override def ++ (elems: Iterable[A]): Multiset[A] = {
    val that: Multiset[A] = iterable2multiset(elems)
    def inner(entries: List[A], result: Multiset[A]): Multiset[A] = entries match { 
      case Nil => result
      case elem :: rest =>
        assert(!result.contains(elem))
        result ++ (int2list(elem,max(this(elem),that(elem))))
    }
    
    inner(elems.toList, empty)
  }
  
  
  override def +++ (elems: Iterable[A]): Multiset[A] = {
    def inner(entries: List[A], result: Map[A,Int]): Map[A,Int] = entries match {
      case Nil => result
      case elem :: rest => result.update(elem,result.getOrElse(elem,0)+1)
    }
    
    new HashMultiset[A](inner(elems.toList,map))
  }
    
  override def --(elems: Iterable[A]): Multiset[A] = {
    def inner(entries: List[A], result: Map[A,Int]): Map[A,Int] = entries match {
      case Nil => result
      case elem :: rest => 
        result.get(elem) match {
          case None => inner(rest,result)
          case Some(n) =>
            assert (n > 0)
            inner(rest, result.update(elem,n-1))
        }
    }  
    
    new HashMultiset[A](inner(elems.toList,map))
  }
  
  override def elements: Iterator[A] = {
    def inner(entries: List[A], result: List[A]): List[A] = entries match {
      case Nil => result
      case elem :: rest =>
        inner(rest, result ::: int2list(elem, this(elem))) 
    }
    
    inner(map.keys.toList, Nil).elements
  }
  
}
