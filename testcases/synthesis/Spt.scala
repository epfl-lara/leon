import leon.lang._
import leon.lang.synthesis._

// Examples taken from http://lara.epfl.ch/~psuter/spt/
object SynthesisProceduresToolkit {

  def e1(a: Nat, b: Nat, c: Nat): Nat = {
    if (b == c) {
      if (a == c) {
        choose { (x: Nat) => x != a }
      } else {
        choose { (x: Nat) => x != a && x != b }
      }
    } else {
      if (a == b) {
        choose { (x: Nat) => x != a && x != c }
      } else {
        choose { (x: Nat) => x != a && x != b && x != c }
      }
    }
  }

  def e2(): (Nat, Nat, Nat) = (Z(), Succ(Z()), Succ(Succ(Succ(Z()))))

  def e3(a1 : Nat, a2 : Nat, a3 : Nat, a4 : Nat): (Nat, Nat) = (a3, a4)

  def e4(a1 : Nat, a2 : Nat, a3 : Nat, a4 : Nat): (Nat, Nat, NatList) = (Succ(a2), a1, Nil())

  def e5(a1 : NatList, a2 : Nat, a3 : NatList): (Nat, NatList, Nat, NatList) = 
    choose { (x1: Nat, x2: NatList, x3: Nat, x4: NatList) =>
      Cons(Succ(x1), x2) == a1 && Succ(x1) != a2 && a3 == Cons(x3, Cons(x3, x4))
    }

  def e6(a: Nat, b: Nat): (Nat, NatList) = {
    if (a == Succ(b)) {
      (Z(), Nil())
    } else {
      leon.lang.error[(Nat, NatList)]("Precondition failed")
    }
  }

  def e7(a1 : NatList, a2 : Nat, a3 : NatList): (Nat, NatList, Nat, NatList) =
    choose { (x1: Nat, x2: NatList, x3: Nat, x4: NatList) =>
      Cons(Succ(x1), x2) == a1 && Succ(x1) != a2 && a3 == Cons(x3, Cons(x3, x4))
    }

  def e8(a : Nat) = a match {
    case Succ(n150) =>
      n150
    case _ =>
      leon.lang.error[(Nat)]("Precondition failed")
  }

  abstract class Nat
  case class Z() extends Nat
  case class Succ(n: Nat) extends Nat

  abstract class NatList
  case class Nil() extends NatList
  case class Cons(head: Nat, tail: NatList) extends NatList

}
