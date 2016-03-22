/* Copyright 2009-2016 EPFL, Lausanne */

package leon.unit.utils

import leon.test._
import leon.purescala.Common._
import leon.utils.StreamUtils._

class StreamsSuite extends LeonTestSuite {
  test("Cartesian Product 1") { ctx =>
    val s1 = FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #:: Stream.empty

    val s2 = FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #:: Stream.empty

    val ss = cartesianProduct(List(s1, s2))

    assert(ss.size === s1.size * s2.size)


  }

  test("Cartesian Product 2") { ctx =>
    val s1 = FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #:: Stream.empty

    val s2 = FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #:: Stream.empty

    val tmp1 = s1.mkString
    val tmp2 = s2.mkString

    val ss = cartesianProduct(List(s1, s2))

    assert(ss.size === s1.size * s2.size)
  }


  test("Cartesian Product 3") { ctx =>
    val s1 = 1 #::
             2 #::
             3 #::
             4 #:: Stream.empty

    val s2 = 5 #::
             6 #::
             7 #::
             8 #:: Stream.empty

    val tmp1 = s1.mkString
    val tmp2 = s2.mkString

    val ss = cartesianProduct(List(s1, s2))

    assert(ss.size === s1.size * s2.size)
  }
}
