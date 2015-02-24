/* Copyright 2009-2014 EPFL, Lausanne */

package leon.test.purescala

import leon._
import leon.test._
import leon.utils.{TemporaryInputPhase, PreprocessingPhase}
import leon.frontends.scalac.ExtractionPhase

import leon.purescala.Common._
import leon.purescala.Trees._
import leon.purescala.Definitions._
import leon.purescala.TypeTrees._
import leon.datagen._
import leon.utils.StreamUtils._

import leon.evaluators._

import org.scalatest.FunSuite

class Streams extends LeonTestSuite {
  test("Cartesian Product 1") {
    val s1 = FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #:: Stream.empty;

    val s2 = FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #:: Stream.empty;

    val ss = cartesianProduct(List(s1, s2))

    assert(ss.size === s1.size * s2.size)


  }

  test("Cartesian Product 2") {
    val s1 = FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #:: Stream.empty;

    val s2 = FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #::
             FreshIdentifier("B", alwaysShowUniqueID = true) #:: Stream.empty;

    val tmp1 = s1.mkString
    val tmp2 = s2.mkString

    val ss = cartesianProduct(List(s1, s2))

    assert(ss.size === s1.size * s2.size)
  }


  test("Cartesian Product 3") {
    val s1 = 1 #::
             2 #::
             3 #::
             4 #:: Stream.empty;

    val s2 = 5 #::
             6 #::
             7 #::
             8 #:: Stream.empty;

    val tmp1 = s1.mkString
    val tmp2 = s2.mkString

    val ss = cartesianProduct(List(s1, s2))

    assert(ss.size === s1.size * s2.size)
  }
}
