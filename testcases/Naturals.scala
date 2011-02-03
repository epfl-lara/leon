import scala.collection.immutable.Set
import funcheck.Annotations._
import funcheck.Utils._

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

  // causes stack overflow with: ./funcheck CAV functions=oneCommut1 testcases/Naturals.scala
    def oneCommut1(x : Nat, y : Nat) : Boolean = {
      plus(x, Succ(y)) == Succ(plus(x,y))
    } holds

    @induct
    def oneCommut(x : Nat, y : Nat) : Boolean = {
      plus(x, Succ(y)) == Succ(plus(x,y))
    } holds

    @induct
    def zeroCommutes(x : Nat) : Boolean = {
      plus(x, Zero()) == plus(Zero(), x)
    } holds

    // we do not know why this inductive proof fails
    @induct
    def commut(x : Nat, y : Nat) : Boolean = {
      plus(x,y) == plus(y, x)
    } holds
}
