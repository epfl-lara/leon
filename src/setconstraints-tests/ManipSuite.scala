package setconstraints

import org.scalatest.FunSuite
import Trees._
import Manip._

class ManipSuite extends FunSuite {

  def v(str: String) = VariableType(str)
  def c(s: SetType) = ComplementType(s)
  def u(sts: SetType*) = UnionType(sts)
  def i(sts: SetType*) = IntersectionType(sts)
  val e = EmptyType
  val a = UniversalType

  test("basic simplify"){
    assert(simplify(u(v("x"), c(v("x")))) === a)
    assert(simplify(i(v("x"), c(v("x")))) === e)
    assert(simplify(u(v("x"), v("y"), v("x"), c(v("x")))) === a)
    assert(simplify(i(v("x"), v("y"), v("x"), c(v("x")))) === e)
    assert(simplify(u(v("x"), v("y"), v("x"), v("x"), u(v("y"), v("x")))) === u(v("x"), v("y")))
  }

  test("basic vars"){
    val vs = Set("x", "y", "z")
    assert(vars(i(u(v("x"), v("x")), i(v("x"), i(v("z"))), v("y"))) == vs)
  }

}
