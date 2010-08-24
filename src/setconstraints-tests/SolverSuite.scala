package setconstraints

import org.scalatest.FunSuite

import Trees._
import Solver._

class SolverSuite extends FunSuite {

  def v(str: String) = VariableType(str)
  def c(s: SetType) = ComplementType(s)
  def u(sts: SetType*) = UnionType(sts)
  def i(sts: SetType*) = IntersectionType(sts)
  def f0 = ConstructorType("f0", Seq())
  def f1(s: SetType) = ConstructorType("f1", Seq(s))
  def f2(s1: SetType, s2: SetType) = ConstructorType("f2", Seq(s1, s2))
  def f3(s1: SetType, s2: SetType, s3: SetType) = ConstructorType("f3", Seq(s1, s2, s3))
//  val constructors = Map("f0" -> 0, "f1" -> 1, "f2" -> 2, "f3" -> 3)
  val v1 = v("v1")
  val v2 = v("v2")
  val v3 = v("v3")
  val e = EmptyType
  val a = UniversalType

  test("is one level"){
    assert(isOneLevel(e))
    assert(!isOneLevel(u(i(e),e)))
    assert(isOneLevel(i(v("x"), v("y"), c(v("z")))))
    assert(isOneLevel(i(f2(i(), i(v("x"), v("z"))))))
    assert(!isOneLevel(f2(i(), i(v("x"), v("z")))))

    val oneLevel = i(c(v("x")), v("y"), f3(i(v("x")), i(), i(v("y"), c(v("z")))))
    assert(isOneLevel(oneLevel))

    assert(isOneLevel(Include(oneLevel, e)))
    assert(!isOneLevel(Include(oneLevel, a)))
  }


  test("to one level"){
    val s1 = Set(Include(f2(v1, v2), v3))
    val constr1 = Map("f1" -> 1, "f2" -> 2)
    println("system:\n" + PrettyPrinter(s1.asInstanceOf[Set[Relation]]))
    val ol1 = oneLevel(s1, constr1)
    println("one level system:\n" + PrettyPrinter(ol1.asInstanceOf[Set[Relation]]))
    assert(isOneLevel(ol1.asInstanceOf[Set[Relation]]))

    val s2 = Set(Include(f1(f1(v1)), v2))
    val constr2 = Map("f1" -> 1)
    println("system:\n" + PrettyPrinter(s2.asInstanceOf[Set[Relation]]))
    val ol2 = oneLevel(s2, constr1)
    println("one level system:\n" + PrettyPrinter(ol2.asInstanceOf[Set[Relation]]))
    assert(isOneLevel(ol2.asInstanceOf[Set[Relation]]))

    val s3 = Set(Include(f2(f1(v1), v2), v3))
    val constr3 = Map("f1" -> 1, "f2" -> 2)
    println("system:\n" + PrettyPrinter(s3.asInstanceOf[Set[Relation]]))
    val ol3 = oneLevel(s3, constr1)
    println("one level system:\n" + PrettyPrinter(ol3.asInstanceOf[Set[Relation]]))
    assert(isOneLevel(ol3.asInstanceOf[Set[Relation]]))
  }

  val constructors = Map("b" -> 0, "c" -> 1)
  def fc(s: SetType) = ConstructorType("c", Seq(s))
  val fb = ConstructorType("b", Seq())
  val system = Set(
    Include(v1, v2),
    Include(fc(v2), c(v2)),
    Include(fc(c(v2)), v2))

  val system2 = Set(
    Include(i(v1, v2, v3), EmptyType),
    Include(i(v1, fb, v3), EmptyType),
    Include(i(v3, v1, fc(v2)), EmptyType)
  )

  test("decreasing order"){
    val decrOrder = decreasingOrder(system2)
    println("decreasing order system:\n" + PrettyPrinter(And(decrOrder.toSeq)))
  }

  val system3 = Set(
    Include(i(c(v2), v1), EmptyType),
    Include(i(v2, fc(v2)), EmptyType),
    Include(i(c(v2), fc(c(v2))), EmptyType)
  )

  test("cascading systems"){
    val cascad = cascadingSystems(oneLevel(system3, constructors), constructors)
    println("cascading systems:\n" + cascad.map(sys => PrettyPrinter(And(sys.toSeq))))
    assert(cascad.forall((system: Set[Include]) => isOneLevel(system.asInstanceOf[Set[Relation]])))
  }

  val constructorsForm = Map("Or" -> 2, "Not" -> 1, "Implies" -> 2)
  val form = VariableType("Formula")
  val ret = VariableType("ret")
  val tmp = VariableType("tmp")
  val or = (f1: SetType, f2: SetType) => ConstructorType("Or", Seq(f1, f2))
  val implies = (f1: SetType, f2: SetType) => ConstructorType("Implies", Seq(f1, f2))
  val not = (f: SetType) => ConstructorType("Not", Seq(f))
  val systemFormula: Set[Relation] = Set(
    //Include(or(form, form), form),
    //Include(implies(form, form), form),
    //Include(not(form), form),
    Include(form, u(or(form, form), not(form), implies(form, form))),
    Include(u(or(form, form), not(form), implies(form, form)), form),
    Include(or(not(ret), ret), tmp),
    Include(not(ret), tmp),
    Include(or(ret, ret), tmp),
    Include(tmp, ret)
    //Include(ret, tmp),
  )



  test("solver"){
  /*
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
    val remTLV = removeTopLevelVars(cascadEq)
    println("no top level vars systems:\n" + remTLV.map(sys => PrettyPrinter(And(sys.toSeq))))
    val solvedSys = solvedForm(remTLV, constructors)
    println("solved form systems:\n" + solvedSys.map(sys => PrettyPrinter(And(sys.toSeq))))
    val fvs = freeVars(solvedSys.head)
    println(fvs)
    */

    println("solving system:\n" + PrettyPrinter(systemFormula))
    val oneLevelSystem = oneLevel(systemFormula.asInstanceOf[Set[Include]], constructorsForm)
    assert(isOneLevel(oneLevelSystem.asInstanceOf[Set[Relation]]))
    println("one level system:\n" + PrettyPrinter(And(oneLevelSystem.toSeq)))
    val decrOrder = decreasingOrder(oneLevelSystem)
    println("decreasing order system:\n" + PrettyPrinter(And(decrOrder.toSeq)))
    val cascad = cascadingSystems(decrOrder, constructorsForm)
    println("cascading systems:\n" + cascad.map(sys => PrettyPrinter(And(sys.toSeq))))
    val cascadEq = cascadingEquations(cascad)
    println("cascading equations systems:\n" + cascadEq.map(sys => PrettyPrinter(And(sys.toSeq))))
    val remTLV = removeTopLevelVars(cascadEq)
    println("no top level vars systems:\n" + remTLV.map(sys => PrettyPrinter(And(sys.toSeq))))
    val solvedSys = solvedForm(remTLV, constructorsForm)
    println("solved form systems:\n" + solvedSys.map(sys => PrettyPrinter(And(sys.toSeq))))
    val fvs = freeVars(solvedSys.head)
    println(fvs)
  }
}
