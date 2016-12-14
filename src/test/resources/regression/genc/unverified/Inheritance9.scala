/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._

object Inheritance9 {

  case class M(var value: Int)

  abstract class Base
  case class X(flag: Boolean) extends Base
  case class Y(m: M) extends Base

  abstract class Base2
  case class V(y: Y) extends Base2
  case class W(v: V)

  case class ArrayWrapper(xs: Array[X])

  def barX(i: X) = 101
  def barY(g: Y) = 202
  def barM(m: M) = { m.value = m.value + 1; 303 }
  def barB(b: Base) = b match {
    case x: X => barX(x)
    case y: Y => barM(y.m) + barY(y)
  }

  def barBfromX(x: X) = barB(x)

  def testCalls(): Int = {
    val y = Y(M(42))

    if (y.m.value == 42) {

      barM(y.m) // y.m.value++

      if (y.m.value == 43) {

        if (barY(y) == 202 && barB(y) == 505) { // y.m.value++

          if (y.m.value == 44) {

            val x = X(true)

            if (barX(x) == barB(x)) {

              if (barBfromX(x) == 101) 0
              else 6

            } else 5

          } else 4

        } else 3

      } else 2

    } else 1
  } ensuring { _ == 0 }

  def generate() = Y(M(0))

  def testAssign(): Int = {
    var x = X(false)
    x = X(true)

    if (x.flag) {

      val array = Array(generate(), generate())

      array(0).m.value = 1

      if (array(1).m.value == 0) {

        barB(array(1))

        if (array(0).m.value == array(1).m.value) {

          val w = W(V(Y(M(1))))

          w.v.y.m.value = 2

          barB(X(true))
          barB(w.v.y)

          if (w.v.y.m.value == 3) 0
          else 40

        } else 30

      } else 20

    } else 10
  } ensuring { _ == 0 }

  def testArrayField(): Int = {
    val a = ArrayWrapper(Array.fill(3)(X(false)))

    if (barX(a.xs(0)) == barB(a.xs(0))) {

      if (barBfromX(a.xs(1)) == 101) {

        if (a.xs(2).flag == false) 0
        else 300

      } else 200

    } else 100
  } ensuring { _ == 0 }

  abstract class SomeBase
  case class SomeDerived(x: Int) extends SomeBase

  abstract class SomeOtherBase
  case class SomeOtherDerived(d: SomeDerived) extends SomeOtherBase

  def zooo(d: SomeDerived) = d.x

  def testNestedConcreteTypes(): Int = {
    val d = SomeDerived(42)
    if (d.x == 42) {

      val d2 = SomeOtherDerived(SomeDerived(58))

      if (d2.d.x == d2.d.x) {
        if (-58 == -(d2.d.x)) {
          if (58 == d2.d.x) {

            if (zooo(d2.d) == d2.d.x) 0
            else 5

          } else 4
        } else 3
      } else 2

    } else 1
  } ensuring { _ == 0 }

  // Because on Unix, exit code should be in [0, 255], we print the exit code on failure
  // and return 1. On success, we do nothing special.
  def printOnFailure(exitCode: Int): Int = {
    if (exitCode == 0) 0
    else {
      implicit val state = leon.io.newState
      leon.io.StdOut.print("Error code: ")
      leon.io.StdOut.print(exitCode)
      leon.io.StdOut.println()
      1
    }
  }

  def _main() = printOnFailure(testCalls + testAssign + testArrayField + testNestedConcreteTypes)

  @extern
  def main(args: Array[String]): Unit = _main()
}

