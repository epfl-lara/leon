package plugin

import funcheck.lib.Specs._


  
object ConsSnoc {
  
  /* Class Hierarchy */
  @generator
  sealed abstract class Lst
  class Cons(val head: Int, val tail: Lst) extends Lst
  class Nill extends Lst

  
  /* Extractors */
  object Nill {
    def apply(): Nill = new Nill()
    def unapply(n: Nill): Boolean = true
  }

  object Cons {
    def apply(head: Int, tail: Lst): Cons = 
      new Cons(head,tail)
    
    def unapply(c: Cons): Option[(Int,Lst)] = 
      Some((c.head,c.tail))
  }
  
  object Snoc {
    def unapply(c: Cons): Option[(Lst,Int)] = c match {
      case Cons(c, xs) => xs  match {
        case Nill() => Some((Nill(),c))
        case Snoc(ys, y) => Some((Cons(c,ys),y))
      }
    }
  }
   
  /*
  object Snoc {
    def unapply(c): Option[(Lst,Int)] = c match {
      case Nill() => None
      case Cons(c, xs) => xs match {
        case Nill() => Some(Tuple2(Nill(),c))
        case Snoc(ys, y) => Some(Tuple2(Cons(c,ys),y))
      }
    }
  }
  */

  def firstAndLast(lst: Lst): Lst = lst match {
    case Nill()             => lst
    case Cons(x, Nill())    => lst
    case Cons(x, Snoc(_,y)) => Cons(x,Cons(y,Nill()))
  }
  
  def main(args: Array[String]) = {}

  /* domain
	    Dom_Nill = Nill &
        Dom_Cons = Cons &
        Dom_Snoc = Cons &
        Dom_Cons \Un Dom_Nill = Lst &
        Dom_Cons \Int Dom_Nill = empty 
  */
  forAll{n: Nill => Nill.unapply(n)} // Dom_Nill = Nill
  forAll{c: Cons => Cons.unapply(c).isDefined} // Dom_Cons = Cons
  forAll{c: Cons => Cons.unapply(c) == Some((c.head, c.tail))} // postcondition for Cons extractor method
  forAll{c: Cons => Snoc.unapply(c).isDefined} // Dom_Snoc = Cons
  forAll{c: Cons => Snoc.unapply(c) == Some((reverse(c).head, reverse(c).tail))} // postcondition for Snoc extractor method
  forAll{l: Lst => lstUnapply(l).isDefined} // Dom_Cons \Un Dom_Nill = Lst 
  forAll{l: Lst => !(lstUnapply(l).get.isInstanceOf[Cons] && lstUnapply(l).get.isInstanceOf[Nill])} //Dom_Cons \Int Dom_Nill = empty 
  
  
  
  def lstUnapply(l: Lst): Option[Any] = l match {
    case n: Nill => Some(Nill.unapply(n))
    case c: Cons => Cons.unapply(c) 
    case _ => None
  }
                                                                                                                                
  def reverse(c: Cons): Cons = {
    def loop(l: Lst, res: Cons): Cons = l match {
      case Nill() => res
      case Cons(head, tail) => loop(tail, Cons(head,res))
    }
    loop(c.tail,Cons(c.head, Nill()))
  }
  
  def equalLst(l1: Lst, l2: Lst): Boolean = (l1,l2) match {
    case (Nill(),Nill()) => true
    case (Cons(x,xs),Cons(y,ys)) if x == y =>
      equalLst(xs,ys)
    case _ => false
  }
  

}