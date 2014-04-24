import leon.lang.invariantLang._

object TreeMaps {
  
  sealed abstract class Tree
  case class Node(left: Tree, value: Int, right: Tree) extends Tree
  case class Leaf() extends Tree

  def size(t: Tree): Int = {
    t match {
      case Leaf() => 0
      case Node(l, x, r) => size(l) + size(r) + 1
    } 
  }
  
  def parallelSearch(elem : Int, t : Tree) : Boolean = {
    t match {      
      case Node(l, x, r) =>
        if(x == elem) true
        else {
          val r1 = parallelSearch(elem, r)
          val r2 = parallelSearch(elem, l)
          if(r1 || r2) true 
          else false
        }
      case Leaf() => false
    }
  } ensuring(res => true template((a,b) => time <= a*size(t) + b))
  
 
  def squareMap(t : Tree) : Tree = {
    t match {      
      case Node(l, x, r) =>
        val nl = squareMap(l)
        val nr = squareMap(r)
        Node(nl, x*x, nr)
      case _ => t
    }
  } ensuring (res => true template((a,b) => time <= a*size(t) + b))
  
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def size(l: List): Int = (l match {
    case Nil() => 0
    case Cons(_, t) => 1 + size(t)
  })   
  
  def fact(n : Int) : Int = {
    require(n >= 0)
    
    if(n == 1 || n == 0) 1
    else n * fact(n-1)
    
  } ensuring(res => true template((a,b) => time <= a*n + b))
  
  def descending(l: List, k: Int) : Boolean = {
    l match {
      case Nil() => true
      case Cons(x, t) => x > 0 && x <= k && descending(t, x-1)
    }
  }
  
  def factMap(l: List, k: Int): List = {
    require(descending(l, k) && k >= 0)
    
   l match {    
    case Nil() => Nil()
    case Cons(x, t) =>  {
      val f = fact(x)
      Cons(f, factMap(t, x-1))      
    }
    
  }} ensuring(res => true template((a,b) => time <= a*(k*k) + b))
} 