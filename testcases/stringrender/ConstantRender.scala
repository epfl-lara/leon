/**
  * Name:     TupleWrapperRender.scala
  * Creation: 15.10.2015
  * Author:   Mikaël Mayer (mikael.mayer@epfl.ch)
  * Comments: Tuple rendering specifications.
  */

import leon.lang._
import leon.annotation._
import leon.collection._
import leon.collection.ListOps._
import leon.lang.synthesis._

object ConstantRender {
  sealed abstract class Thread
  case class T1() extends Thread
  case class T2() extends Thread
  case class T3() extends Thread

  @inline def psStandard(s: Thread) = (res: String) => (s, res) passes {
    case T1() => "T1"
  }
  
  @inline def psSuffix(s: Thread) = (res: String) => (s, res) passes {
    case T1() => "T1()"
  }
  
  @inline def psPrefix(s: Thread) = (res: String) => (s, res) passes {
    case T1() => "Call: T1()"
  }
  
  def synthesizeStandard(s: Thread): String = {
     ???[String]
  } ensuring psStandard(s)
  
  def synthesizeSuffix(s: Thread): String = {
     ???[String]
  } ensuring psSuffix(s)
  
  def synthesizePrefix(s: Thread): String = {
     ???[String]
  } ensuring psPrefix(s)
}