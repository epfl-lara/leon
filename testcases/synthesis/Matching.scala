import leon.lang._
import leon.lang.synthesis._

object Matching {
  def t1(a: NatList) = choose( (x: Nat) => Cons(x, Nil()) == a)

  abstract class Nat
  case class Z() extends Nat
  case class Succ(n: Nat) extends Nat

  abstract class NatList
  case class Nil() extends NatList
  case class Cons(head: Nat, tail: NatList) extends NatList
}
