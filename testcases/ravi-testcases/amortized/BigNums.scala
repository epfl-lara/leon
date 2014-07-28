import leon.lang.invariantLang._

object BigNums {
  sealed abstract class BigNum
  case class Cons(head: Int, tail: BigNum) extends BigNum
  case class Nil() extends BigNum   
  
  def incrTime(l: BigNum) : Int = {
    l match {
      case Nil() => 1    
      case Cons(x, tail) => 
        if(x == 0) 1
        else 1 + incrTime(tail)
    }
  }
  
  def potentialIncr(l: BigNum) : Int = {
    l match {
      case Nil() => 0
      case Cons(x, tail) => 
        if(x == 0) potentialIncr(tail)
        else 1 + potentialIncr(tail)
    }
  } 
  
  def increment(l: BigNum) : BigNum = {
    l match {
      case Nil() => Cons(1,l)
      case Cons(x, tail) => 
        if(x == 0) Cons(1, tail)
        else Cons(0, increment(tail)) 
    }
  } ensuring (res => true template((a,b,c) => (time <= a*incrTime(l) + b) && (incrTime(l) + potentialIncr(res) - potentialIncr(l) <= c)))
    //potentialIncr(res) <= potentialIncr(l)+1 )
  
  /**
   * Nop is the number of operations
   */
  def incrUntil(nop: Int, l: BigNum) : BigNum = {
    if(nop == 0)  l
    else {
      incrUntil(nop-1, increment(l))  
    }
  } ensuring (res =>  true template((a,b,c) => time <= a*nop + b*potentialIncr(l)+c))
  
  def count(nop: Int) : BigNum = {      
    incrUntil(nop, Nil())    
  } ensuring (res =>  true template((a,b) => time <= a*nop + b))
  
}
