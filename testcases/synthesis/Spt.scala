import leon.Utils._

// Examples taken from http://lara.epfl.ch/~psuter/spt/
object SynthesisProceduresToolkit {

  def e1(a: Nat, b: Nat, c: Nat): Nat = choose( (x: Nat) => x != a && x != b && x != c)

  def e2(): (Nat, Nat, Nat) = choose( (x: Nat, y: Nat, z: Nat) => x != y && y != z && x != z)

  def e3(a1 : Nat, a2 : Nat, a3 : Nat, a4 : Nat): (Nat, Nat) = choose( (x1 : Nat, x2 : Nat) => Cons(x1, Cons(x2, Nil())) == Cons(a3, Cons(a4, Nil())) && Cons(a1,  Cons(a2, Nil())) != Cons(x1, Cons(x2, Nil())))

  def e4(a1 : Nat, a2 : Nat, a3 : Nat, a4 : Nat): (Nat, Nat, NatList) = choose( (x1 : Nat, x2 : Nat, x3 : NatList) => Cons(x1, Cons(x2, Nil())) != Cons(a1, Cons(a2, Nil())))

  def e5(a1 : NatList, a2 : Nat, a3 : NatList): (Nat, NatList, Nat, NatList) = choose( (x1 : Nat, x2 : NatList, x3 : Nat, x4 : NatList) => Cons(Succ(x1), x2) == a1 && Succ(x1) != a2 && a3 == Cons(x3, Cons(x3,  x4)))

  def e6(a: Nat, b: Nat): (Nat, NatList) = choose( (x: Nat, y: NatList) => a == Succ(b))

  def e7(a1 : NatList, a2 : Nat, a3 : NatList): (Nat, NatList, Nat, NatList) = choose( (x1 : Nat, x2 : NatList, x3 : Nat, x4 : NatList) =>
    Cons(Succ(x1), x2) == a1 && Succ(x1) != a2 && a3 == Cons(x3, Cons(x3,  x4)) || (a1 == a3 && x1 == x3))

  def e8(a : Nat) = choose { (x : Nat) => Succ(x) == a }

  abstract class Nat
  case class Z() extends Nat
  case class Succ(n: Nat) extends Nat

  abstract class NatList
  case class Nil() extends NatList
  case class Cons(head: Nat, tail: NatList) extends NatList

}
