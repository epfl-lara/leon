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
    
    //def unapply(n: Nill): Boolean = true
    def unapply(l: Lst): Boolean = l match {
      case n: Nill => true
      case c: Cons => false
    }
  }

  object Cons {
    def apply(head: Int, tail: Lst): Cons = new Cons(head,tail)
    
    //def unapply(c: Cons): Option[(Int,Lst)] = Some((c.head,c.tail))
    def unapply(l: Lst): Option[(Int,Lst)] = l match {
      case n: Nill => None
      case c: Cons => Some((c.head,c.tail)) 
    } 
      
  }
  
  object Snoc {
    def unapply(l: Lst): Option[(Lst,Int)] = l match {
      case Nill() => None
      case Cons(c, xs) => xs match {
        case Nill() => Some((Nill(),c))
        case Snoc(ys, y) => Some((Cons(c,ys),y))
      }
    }
  }
  
  /*
  object Snoc {
    def unapply(c: Cons): Option[(Lst,Int)] = c match {
      case Cons(c, xs) => xs  match {
        case Nill() => Some((Nill(),c))
        case Snoc(ys, y) => Some((Cons(c,ys),y))
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
  forAll{c: Cons => Snoc.unapply(c).isDefined} // Dom_Snoc = Cons
  
  // partition
  forAll{l: Lst => Cons.unapply(l).isDefined || Nill.unapply(l)} // Dom_Cons \Un Dom_Nill = Lst 
  forAll{l: Lst => !(Cons.unapply(l).isDefined && Nill.unapply(l))} //Dom_Cons \Int Dom_Nill = empty
  // the two above properties could be simmply be written as
  //forAll{l: Lst => Cons.unapply(l).isDefined ^^ Nill.unapply(l)} 
  
  /* axioms */  
  forAll[(Int,Lst)]{ p => equalCons(Cons.unapply(Cons(p._1,p._2)), Some(p._1,p._2))}
  
  def equalCons(p1: Option[(Int,Lst)], p2: Option[(Int,Lst)]): Boolean = (p1,p2) match {
    case (None,None) => true
    case (Some((x,xs)), Some((y,ys))) => 
      equalLst(Cons(x,xs),Cons(y,ys))
    case _ => false
  }
  
  def equalLst(l1: Lst, l2: Lst): Boolean = (l1,l2) match {
    case (Nill(),Nill()) => true
    case (Cons(x,xs),Cons(y,ys)) if x == y =>
      equalLst(xs,ys)
    case _ => false
  }
  

}