package funcheck

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

  def firstAndLast(lst: Lst): Lst = lst match {
    case Nill()             => lst
    case Cons(x, Nill())    => lst
    case Cons(x, Snoc(_,y)) => Cons(x,Cons(y,Nill()))
  }
  
 

  
  // Nill extractor always succeed for Nill instances
  forAll{n: Nill => Nill.unapply(n)}             
  // Cons extractor always succeed for Cons instances
  forAll{c: Cons => Cons.unapply(c).isDefined}   
  // Cons extractor succeed iff the passed object instance is of type Cons
  forAll{l: Lst => Cons.unapply(l).isEmpty || (Cons.unapply(l).isDefined && l.isInstanceOf[Cons]) }
  // Snoc extractor always succeed for Cons instances
  forAll{c: Cons => Snoc.unapply(c).isDefined} 
  // Snoc extractor succeed iff the passed object instance is of type Cons
  forAll{l: Lst => Cons.unapply(l).isEmpty || (Snoc.unapply(l).isDefined && l.isInstanceOf[Cons])}
  
  /* These are postconditions, but they are checked as program axioms */
  // Check behavior of Cons extractor 
  forAll{c: Cons => equalLst(cons(Cons.unapply(c).get), c)}
  // Check behavior of Snoc extractor  
  forAll{c: Cons => equalLst(concat(Snoc.unapply(c).get), c) }
  
  // partition
  // For any Lst, either the Cons or the Nill extractor applies
  forAll{l: Lst => Cons.unapply(l).isDefined || Nill.unapply(l)} 
  // For any Lst, it is never the case that both the Cons and the Nill extractor applies
  forAll{l: Lst => !(Cons.unapply(l).isDefined && Nill.unapply(l))} 
  // the two above properties could be simmply be written as
  //forAll{l: Lst => Cons.unapply(l).isDefined ^^ Nill.unapply(l)} 
  
  /* list axioms */  
  forAll[(Int,Cons)]{ p => (Cons.unapply(Cons(p._1,p._2)).get._1 == p._1) && 
                           equalLst(Cons.unapply(Cons(p._1,p._2)).get._2, p._2) }
  forAll[(Int, Cons)] { p => Cons(p._1,p._2).head == p._1}
  forAll[(Int, Cons)] { p => Cons(p._1,p._2).tail == p._2}
  
  
  def cons(s: (Int,Lst)): Cons = Cons(s._1, s._2)
  
  def concat(c: (Lst, Int)): Lst = c._1 match {
    case Nill() => Cons(c._2, Nill())
    case Cons(x,xs) => Cons(x,concat(xs,c._2))
  }
  
  def equalLst(l1: Lst, l2: Lst): Boolean = (l1,l2) match {
    case (Nill(),Nill()) => true
    case (Cons(x,xs),Cons(y,ys)) if x == y =>
      equalLst(xs,ys)
    case _ => false
  }
  
  def main(args: Array[String]) = {}
}