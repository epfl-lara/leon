/* Viktor Kuncak, 2015-08-27
   I tried to formalize linear bijection function for nested lists,
   based on the paper:

   Ivan Kuraj, Viktor Kuncak, and Daniel Jackson. 
   Programming with enumerable sets of structures. In OOPSLA, 2015.

   Leon found a counterexample (which I did not quite understand), but
   then synthesized an untrusted solution that looked similar (a bit
   more concise in a few places) and had the role of two elements of
   the tuple reversed. This made me realize I confused the order of
   elements in the tuple.

*/
import leon.lang._
import leon.annotation._
import leon.collection._
import leon.collection.ListOps._
import leon.lang.synthesis._

object DisperseBijection { 
  def totalSize[A](l: List[List[A]]): BigInt = {
    l.map(_.size).foldRight(BigInt(0))(_ + _)
  } ensuring(res => res >= 0)
  
  def lin1[A](l: List[List[A]], i : BigInt): (BigInt, BigInt) = {
    require (0 <= i && i < totalSize(l))
    l match {
      case Cons(h, t) => {
        val s = h.size
        if (i < s) (i, BigInt(0))
        else {
          val (x1,y1) = lin1[A](t, i-s)
          (x1, y1+1)
        }
      }
    }
  }.ensuring((res:(BigInt,BigInt)) => { res match {
    case (x,y) => { 
      BigInt(0) <= x && x < l.size && l(x)(y) == flatten(l)(i)
    }
  }})

}