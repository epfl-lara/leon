/* Copyright 2009-2016 EPFL, Lausanne */

package leon.unit.utils

import leon.test._

import leon.utils._

class UtilsSuite extends LeonTestSuite {

  test("fixpoint computes correct fixpoint of function that increments up to a max") { ctx =>
    def f(x: Int): Int = if(x < 10) x + 1 else 10
    assert(f(10) === 10)
    assert(fixpoint(f)(1) === 10)
  }

  test("fixpoint computes correct fixpoint with a large limit") { ctx =>
    def f(x: Int): Int = if(x < 100) x + 1 else 100
    assert(f(100) === 100)
    assert(fixpoint(f)(-1) === 100)
  }

  test("fixpoint finds the fixpoint in small number of iteration") { ctx =>
    def f(x: Int): Int = if(x < 10) x + 1 else 10
    assert(f(10) === 10)
    assert(fixpoint(f, 15)(1) === 10)
  }

  test("fixpoint of id is the starting expression") { ctx =>
    def id(x: Int): Int = x
    assert(fixpoint(id)(1) === 1)
    assert(fixpoint(id)(42) === 42)
  }

}
