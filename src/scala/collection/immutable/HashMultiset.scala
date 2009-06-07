package scala.collection.immutable

object HashMultiset {
  
  /** The empty multiset of this type. */
  def empty[A]: Multiset[A] = new EmptyMultiset[A]
  
  /** The canonical factory for this type */
  def apply[A](elems: A*) = empty[A] ++ elems
}

class HashMultiset[A] private[immutable] (private val map: Map[A,Int]) extends Multiset[A] with Helper[A] {
  
  def empty[C]: Multiset[C] = new EmptyMultiset[C]
  
  override def size: Int = map.values.foldLeft(0)((a,b) => a+b)
  
  override def apply(elem: A): Int = map.getOrElse(elem,0)
    
  override def intersect (that: collection.Multiset[A]): Multiset[A] = {
    def inner(entries: List[A], result: Map[A,Int]): Map[A,Int] = entries match {
      case Nil => result
      case elem :: rest => inner(rest, result.update(elem, min(this(elem),that(elem))))
    }
    
    new HashMultiset[A](inner(asSet.toList,new HashMap[A,Int].empty))
  }
  
  
  override def ++ (elems: Iterable[A]): Multiset[A] = {
    val that = iterable2multiset(elems)
    
    def inner(entries: List[A], result: Map[A,Int]): Map[A,Int] = entries match {
      case Nil => result
      case elem :: rest =>
        inner(rest, result.update(elem,max(result.getOrElse(elem,0),that(elem))))
    }
    
    new HashMultiset[A](inner(that.asSet.toList, map))
  }
  
  
  override def +++ (elems: Iterable[A]): Multiset[A] = {
    def inner(entries: List[A], result: Map[A,Int]): Map[A,Int] = entries match {
      case Nil => result
      case elem :: rest => result.update(elem,result.getOrElse(elem,0)+1)
    }
    
    new HashMultiset[A](inner(elems.toList,map))
  }
    
  override def --(elems: Iterable[A]): Multiset[A] = {
    val that = iterable2multiset(elems)
    def inner(entries: List[A], result: Map[A,Int]): Map[A,Int] = entries match {
      case Nil => result
      case elem :: rest => 
        val diff = result.getOrElse(elem,0) - that(elem)
        if(diff > 0)
          inner(rest, result.update(elem,diff))
        else
          inner(rest, result - elem)
    }  
    
    new HashMultiset[A](inner(that.asSet.toList,map))
  }
  
  override def elements: Iterator[A] = {
    def inner(entries: List[A], result: List[A]): List[A] = entries match {
      case Nil => result
      case elem :: rest =>
        inner(rest, result ::: int2list(elem, this(elem))) 
    }
    
    inner(map.keys.toList, Nil).elements
  }
  
  override def asSet: Set[A] = HashSet.empty[A] ++ map.keys
  
}
