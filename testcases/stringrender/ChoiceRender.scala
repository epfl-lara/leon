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

object ChoiceRender {
  sealed abstract class Thread
  case class T1() extends Thread
  case class T2() extends Thread
  case class T3() extends Thread
  
  sealed abstract class Action
  case class Call(t: Thread, args: Option[Int]) extends Action

  @inline def psStandard(s: Action) = (res: String) => (s, res) passes {
    case Call(T1(),None()) => "T1 call"
    case Call(T1(),Some(2)) => "T1 -> 2"
  }
  
  def synthesizeStandard(s: Action): String = {
     ???[String]
  } ensuring psStandard(s)
}