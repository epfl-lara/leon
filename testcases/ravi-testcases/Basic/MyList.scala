object MyList {

  abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  sealed abstract class Pair
  case class ListPair(l: List, time: Int) extends Pair
  
  def size(l: List): Int = (l match {
    case Cons(_, tail) => 1 + size(tail)
    case Nil() => 0
  }) ensuring (_ >= 0)
  
  def insert(l: List, e: Int): ListPair = (l match {    
    case Cons(n,tail) => { 
    	val newtail = insert(tail,e)
        ListPair(Cons(n,newtail.l),newtail.time + 1)         
    }
    case Nil() => ListPair(Cons(e,Nil()),0)
  }) ensuring (res => { res.time == size(l)})
  
  /*def insertWOPost(l: List, e: Int): ListPair = (l match {    
    case Cons(n,tail) => { 
    	val newtail = insertWOPost(tail,e)
        ListPair(Cons(n,newtail.l),newtail.time + 1)         
    }
    case Nil() => ListPair(Cons(e,Nil()),0)
  }) 
    
  def insertWOPostClient(l: List, e: Int): ListPair = (
      //insertWOPost(l,e)
      insert(l,e)
  ) ensuring (res => { res.time == size(l)})*/  
  
  def traverse(l: List): Int = (l match {    
    case Cons(n,tail) => { 
    	traverse(tail) + 1         
    }
    case Nil() => 0
  }) ensuring (res => res == size(l))
  
  def ContrivedInsert(l: List, orig: List, e: Int): ListPair = (l match {    
    case Cons(n,tail) => { 
    	val p1 = traverse(orig)    	
    	val p2 = ContrivedInsert(tail,orig,e)
    	ListPair(Cons(n,p2.l),p2.time + p1)
    }
    case Nil() => ListPair(Cons(e,Nil()),0)
  }) ensuring (res => { res.time == size(l) * size(orig)})
  
   def main(args: Array[String]): Unit = {
    val l:List = Cons(7,Cons(3,Cons(2,Nil())))
    //val newl = insert(l,3)
    val newl = ContrivedInsert(l,l,3)
	println(newl.time)
	println(size(l))
	printlist(newl.l)
  }
  
    def printlist(l: List) : Unit = l match {
      case Cons(n,tail) => {
        print(n+",")
        printlist(tail)
      }
      case Nil() => println()
    }
}
