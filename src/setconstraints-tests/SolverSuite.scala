package setconstraints

import org.scalatest.FunSuite

import Trees._
import Solver._

class SolverSuite extends FunSuite {

  def v(str: String) = VariableType(str)
  def c(s: SetType) = ComplementType(s)
  def u(sts: SetType*) = UnionType(sts)
  def i(sts: SetType*) = IntersectionType(sts)
  def f(sts: SetType*) = ConstructorType("f", sts)
  val e = EmptyType
  val a = UniversalType

  test("is one level"){
    assert(isOneLevel(e))
    assert(!isOneLevel(u(i(e),e)))
    assert(isOneLevel(i(v("x"), v("y"), c(v("z")))))
    assert(isOneLevel(i(f(i(), i(v("x"), v("z"))))))
    assert(!isOneLevel(f(i(), i(v("x"), v("z")))))

    val oneLevel = i(c(v("x")), v("y"), f(i(v("x")), i(), i(v("y"), c(v("z")))))
    assert(isOneLevel(oneLevel))

    assert(isOneLevel(Include(oneLevel, e)))
    assert(!isOneLevel(Include(oneLevel, a)))
  }

  val constructors = Map("b" -> 0, "c" -> 1)
  def fc(s: SetType) = ConstructorType("c", Seq(s))
  val fb = ConstructorType("b", Seq())
  val x1 = v("x1")
  val x2 = v("x2")
  val x3 = v("x3")
  val system = Set(
    Include(x1, x2),
    Include(fc(x2), c(x2)),
    Include(fc(c(x2)), x2))


  test("to one level"){
    val oneLevelSystem = oneLevel(system, constructors)
    println("one level system:\n" + PrettyPrinter(And(oneLevelSystem.toSeq)))
    assert(isOneLevel(oneLevelSystem.asInstanceOf[Set[Relation]]))
  }

  val system2 = Set(
    Include(i(x1, x2, x3), EmptyType),
    Include(i(x1, fb, x3), EmptyType),
    Include(i(x3, x1, fc(x2)), EmptyType)
  )

  test("decreasing order"){
    val decrOrder = decreasingOrder(system2)
    println("decreasing order system:\n" + PrettyPrinter(And(decrOrder.toSeq)))
  }

  val system3 = Set(
    Include(i(c(x2), x1), EmptyType),
    Include(i(x2, fc(x2)), EmptyType),
    Include(i(c(x2), fc(c(x2))), EmptyType)
  )

  test("cascading systems"){
    val cascad = cascadingSystems(oneLevel(system3, constructors), constructors)
    println("cascading systems:\n" + cascad.map(sys => PrettyPrinter(And(sys.toSeq))))
    assert(cascad.forall((system: Set[Include]) => isOneLevel(system.asInstanceOf[Set[Relation]])))
  }

  test("solver"){
    println("solving system:\n" + PrettyPrinter(And(system.toSeq)))
    val oneLevelSystem = oneLevel(system, constructors)
    println("one level system:\n" + PrettyPrinter(And(oneLevelSystem.toSeq)))
    assert(isOneLevel(oneLevelSystem.asInstanceOf[Set[Relation]]))
    val decrOrder = decreasingOrder(oneLevelSystem)
    println("decreasing order system:\n" + PrettyPrinter(And(decrOrder.toSeq)))
    val cascad = cascadingSystems(decrOrder, constructors)
    println("cascading systems:\n" + cascad.map(sys => PrettyPrinter(And(sys.toSeq))))
    val cascadEq = cascadingEquations(cascad)
    println("cascading equations systems:\n" + cascadEq.map(sys => PrettyPrinter(And(sys.toSeq))))
  }
}
