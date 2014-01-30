import leon.Utils._

object SpeedBenchmarks {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def size(l: List): Int = (l match {
    case Nil() => 0
    case Cons(_, t) => 1 + size(t)
  })   
  
  sealed abstract class StringBuffer
  case class Chunk(str: List, next: StringBuffer) extends StringBuffer
  case class Empty() extends StringBuffer
  
  def length(sb: StringBuffer) : Int = sb match {
    case Chunk(_, next) => 1 + length(next)
    case _ => 0
  }
    
  def sizeBound(sb: StringBuffer, k: Int) : Boolean ={
    sb match {
      case Chunk(str, next) => size(str) <= k && sizeBound(next, k)
      case _ => 0 <= k
    }
  }
  
  def mult(x : Int, y : Int) : Int = {
      if(x == 0 || y == 0) 0
      else
    	  mult(x,y-1) +  x 
  } 
  
  /**
   * The functional version of the implementation given in Fig 1 of SPEED 
   */
  def EqualsChunk(str1: List, str2: List, k : Int) : (Boolean, (List, List)) = {
    require(size(str1) <= k && size(str2) <= k)  
  
    (str1, str2) match {
      case (Cons(h1,t1), Cons(h2,t2)) => {
        if(h1 != h2) (false, (t1,t2))
        else EqualsChunk(t1, t2, k)
      }
      case _ => (true, (str1, str2))
    }
  } ensuring(res => (size(res._2._1) <= k && size(res._2._2) <= k)) 
  
  def loadNextChunk(s: StringBuffer, k: Int) : (List, StringBuffer) = {     
    require(sizeBound(s,k))  
  
    s match {
      case Chunk(Nil(), next)  => loadNextChunk(next, k)
      case Chunk(str, next) => (str, next)
      case _ => (Nil(), Empty())
    }
  } ensuring(res => (sizeBound(res._2,k) && (res._1 == Nil() || (size(res._1) <= k && length(res._2) <= length(s) - 1))))

  def Equals(str1: List, str2: List, s1: StringBuffer, s2: StringBuffer, k: Int): Boolean = {
    require(sizeBound(s1, k) && sizeBound(s2, k) && size(str1) <= k && size(str2) <= k)

    val (res, newstrs) = EqualsChunk(str1, str2, k)
    if (res == false) false
    else {
      val (nstr1, nstr2) = newstrs
      val (fstr1, sb1) =
        if (nstr1 == Nil())
          loadNextChunk(s1, k)
        else
          (nstr1, s1)
      val (fstr2, sb2) =
        if (nstr2 == Nil())
          loadNextChunk(s2, k)
        else
          (nstr2, s2)
      fstr1 match {
        case Nil() => fstr2 == Nil()
        case _ => {
          if (fstr2 == Nil()) false
          else {
            Equals(fstr1, fstr2, sb1, sb2, k)
          }
        }
      }
    }
  } ensuring (res => true)

/*  def reverseRec(l1: List, l2: List): List = (l1 match {
    case Nil() => l2
    case Cons(x, xs) => reverseRec(xs, Cons(x, l2))

  }) ensuring (res =>  size(l1) + size(l2) == size(res) template((a,b) => time <= a*size(l1) + b))

  def reverse(l: List): List = {
    reverseRec(l, Nil())
    
  } ensuring (res => size(l) == size(res) template((a,b) => time <= a*size(l) + b))*/

}
