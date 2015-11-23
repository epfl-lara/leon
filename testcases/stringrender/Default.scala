/**
  * Name:     Default.scala
  * Creation: 15.10.2015
  * Author:   Mikaël Mayer (mikael.mayer@epfl.ch)
  * Comments: Benchmark for solving default string transformation problems.
  */

import leon.lang._
import leon.annotation._
import leon.collection._
import leon.collection.ListOps._
import leon.lang.synthesis._

/**
 * @author Mikael
 */
object Default {
  @inline def psIntStandard(s: Int) = (res: String) => (s, res) passes {
    case 1 => "1"
    case 42 => "42"
    case -3 => "-3"
  }
  
  @inline def psBigIntStandard(s: BigInt) = (res: String) => (s, res) passes {
    case BigInt(1) => "1"
    case BigInt(42) => "42"
    case BigInt(-3) => "-3"
  }
  
  @inline def psBooleanStandard(s: Boolean) = (res: String) => (s, res) passes {
    case true => "true"
    case false => "false"
  }
  
  @inline def psBoolean2(s: Boolean) = (res: String) => (s, res) passes {
    case true => "yes"
    case false => "no"
  }
  
  def synthesizeIntStandard(s: Int): String = {
    ???[String]
  } ensuring psIntStandard(s)
  
  def synthesizeBigIntStandard(s: BigInt): String = {
    ???[String]
  } ensuring psBigIntStandard(s)
  
  def synthesizeBooleanStandard(s: Boolean): String = {
    ???[String]
  } ensuring psBooleanStandard(s)
  
  def synthesizeBoolean2(s: Boolean): String = {
    ???[String]
  } ensuring psBoolean2(s)
}