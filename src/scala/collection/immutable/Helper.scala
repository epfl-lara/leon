package scala.collection.immutable

private[immutable] trait Helper[A] {
  
  protected def int2list[C](elem: C, times: Int): List[C] = {
    require(times >= 0)
    if(times == 0)
      Nil
    else
      elem :: int2list(elem,times-1)
  }
  
  protected def iterable2multiset(elems: Iterable[A]): Multiset[A] = {
    def inner(elems: List[A], result: Map[A,Int]): Map[A,Int] = elems match {
      case Nil => result
      case elem :: tail => inner(tail, result.update(elem, result.getOrElse(elem,0) + 1)) 
    }
    new HashMultiset[A](inner(elems.toList,new scala.collection.immutable.HashMap[A,Int].empty))
  }
  
  protected def min(a: Int, b: Int): Int = if(a <= b) a else b
  protected def max(a: Int, b: Int): Int = if(a < b) b else a

}
