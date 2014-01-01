import leon.Utils._
import scala.collection.immutable.Map

object ObsPure {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List
  
  def content(l: List) : Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(x, xs) => Set(x) ++ content(xs)
  }
    
  //Move to front
  def findAndRemove(key: Int, l: List) : (Boolean, List) = {l match {
    case Nil() => (false, l)
    case Cons(x, tail) => {
      if(key == x) (true, tail) 
      else {
        val (found, newTail) = findAndRemove(key, tail)
        (found, Cons(x, newTail))
      }    
    }
  }} ensuring(res => (if(res._1) (content(l) -- Set(key)).subsetOf(content(res._2)) && (content(res._2)).subsetOf(content(l))
		  			else content(res._2) == content(l)) &&
		  			(!res._1 || Set(key).subsetOf(content(l))) &&
		  			(!Set(key).subsetOf(content(l)) || res._1)
    )
  
  def findAndMoveToFront(key : Int, l: List): (Boolean, List) = {
    val (found, newl) = findAndRemove(key, l)
    (found, if(found) Cons(key, newl) else newl) 
    
  } ensuring(res => content(res._2) == content(l) &&
      (!res._1 || Set(key).subsetOf(content(l))) &&
      (!Set(key).subsetOf(content(l)) || res._1)
      )
      
    
  //havocs the state.
  def havoc(l: List): List = {    
    if (nondet[Boolean]) {      
      val (_, newl) = findAndMoveToFront(nondet[Int], l)
      havoc(newl)      
    } else {
      l
    }
  } ensuring(res => content(res) == content(l))   
 
  def purityChecker(): (Boolean, Boolean) = {
    
    val l = nondet[List]   
    val x = nondet[Int]
    val (res1, nextl) = findAndMoveToFront(x, l)
    val laterl = havoc(nextl)
    val (res2, _) = findAndMoveToFront(x, laterl)
    (res1, res2)

  } ensuring (res => res._1 == res._2)
}
