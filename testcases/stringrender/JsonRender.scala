/** 
  * Name:     JsonRender.scala
  * Creation: 25.11.2015
  * Author:   Mikael Mayer (mikael.mayer@epfl.ch)
  * Comments: Json specifications
  */

import leon.lang._
import leon.annotation._
import leon.collection._
import leon.collection.ListOps._
import leon.lang.synthesis._

object JsonRender {
  /** Synthesis by example specs */
  @inline def psStandard(x: Int, y: String, z: Boolean) = (res: String) =>((x, y, z), res) passes {
    case (31, "routed", true) => """{ field1: 31, field2: "routed", field3: true }"""
  }
  
  @inline def psTupled1(xy: (Int, String), z: Boolean) = (res: String) =>((xy, z), res) passes {
    case ((31, "routed"), true) => """{ field1: 31, field2: "routed", field3: true }"""
  }

  @inline def psTupled2(x: Int, yz: (String, Boolean)) = (res: String) =>((x, yz), res) passes {
    case (31, ("routed", true)) => """{ field1: 31, field2: "routed", field3: true }"""
  }
  
  //////////////////////////////////////////////
  // Non-incremental examples: pure synthesis //
  //////////////////////////////////////////////
  def synthesizeStandard(x: Int, y: String, z: Boolean): String = {
    ???[String]
  } ensuring psStandard(x, y, z)

  def synthesizeTupled1(xy: (Int, String), z: Boolean): String = {
    ???[String]
  } ensuring psTupled1(xy, z)
  
  def synthesizeTupled2(x: Int, yz: (String, Boolean)): String = {
    ???[String]
  } ensuring psTupled2(x, yz)
}