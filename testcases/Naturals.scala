import scala.collection.immutable.Set
import leon.annotation._
import leon.lang._

object Naturals {
    sealed abstract class Nat
    case class Zero() extends Nat
    case class Succ(x : Nat) extends Nat

    def plus(x : Nat, y : Nat) : Nat = {
      x match {
                case Zero() => y
                case Succ(x1) => Succ(plus(x1, y))
      }
    }

    def leftZero(y : Nat) : Boolean = {
      plus(Zero(), y) == y
    } holds

    @induct
    def rightZero(x : Nat) : Boolean = {
      plus(x, Zero()) == x
    } holds

    @induct
    def assoc(x : Nat, y : Nat, z : Nat) : Boolean = {
      plus(x, plus(y,z)) == plus(plus(x, y), z)
    } holds

    @induct
    def zeroCommutes(x : Nat) : Boolean = {
      plus(Zero(), x) ==  plus(x, Zero()) 
    } holds


// induction is made on first parameter
//induction on x works here!
//induction on y = stack overflow
    @induct
    def oneCommut(x : Nat, y : Nat) : Boolean = {
      Succ(plus(x,y)) ==  plus(x, Succ(y))
    } holds

    @induct
    def inductionStep1(x : Nat, y : Nat) : Boolean = {
      plus(Succ(y),x) == Succ(plus(y,x))
    } holds


        //we need simplification !
        //(x.isInstanceOf[Zero] ==> (plus(x, y) == plus(y, x)))  this base case does not work even if it is above!!
    // we do not know why this inductive proof fails
    @induct
    def commut(x : Nat, y : Nat) : Boolean = {
      plus(x,y) == plus(y, x)
    } holds
}
