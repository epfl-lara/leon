import leon.lang.synthesis._

object Naturals {
  
  abstract class Nat {
    def intValue : Int = { this match {
      case Zero => 0
      case Succ(n) => n.intValue + 1
    }} ensuring { _ >= 0 }

    def +(that : Nat) : Nat = { this match {
      case Zero => that
      case Succ(n) => n + Succ(that)
    }} ensuring { _.intValue == this.intValue + that.intValue }

    def <=(that : Nat) : Boolean = { (this, that) match {
      case (Zero, _) => true
      case (_, Zero) => false
      case (Succ(n1), Succ(n2)) => n1 <= n2
    }} ensuring { _ == this.intValue <= that.intValue }

    def >(that : Nat) = !(this <= that)

    def -(that : Nat) : Nat = {
      require(that <= this)
      (this, that) match {
        case (_, Zero) => this
        case (Succ(n1), Succ(n2)) => n1 - n2
      }
    } ensuring { _.intValue == this.intValue - that.intValue }

    def * (that: Nat) : Nat = { this match {
      case Zero => Zero
      case Succ(n) => that + n * that
    }} ensuring { _.intValue == this.intValue * that.intValue }
    
    /*
    def /(that : Nat) : Nat = {
      require(that > Zero)
      if (that <= this) (this - that)/ that + one
      else Zero
    } ensuring { _.intValue == this.intValue / that.intValue }

    def %(that : Nat) : Nat = {
      require(that > Zero)
      this - (this / that) * that
    } ensuring { _.intValue == this.intValue % that.intValue }
    
    // Convension : least s. digit first
    def isDecimalRepr(l : List[Nat]) : Boolean = l match {
      case Nil() => false
      case Cons(h, t) => h <= ten && isDecimalRepr(t)
    }

    def decimalToNat(l : List[Nat]) : Nat = {
      require(isDecimalRepr(l))
      l match {
        case Cons(h, Nil()) => h
        case Cons(h, t) => 10 * decimalToNat(t) + h
      }
    }

    */

  }
  case object Zero extends Nat
  case class Succ(n : Nat) extends Nat

  def ten = {
    val two = Succ(Succ(Zero))
    val five = Succ(two + two)
    two * five
  }

  def fortyTwo = { 
    val one = Succ(Zero)
    val two = one + one
    val three = two + one
    val seven = (two * three) + one
    two * three * seven 
  } ensuring { _.intValue == 42 }

}
