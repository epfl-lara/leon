/** 
  * Name:     ListRender.scala
  * Creation: 14.10.2015
  * Author:   Mika�l Mayer (mikael.mayer@epfl.ch)
  * Comments: First benchmark ever for solving string transformation problems. List specifications.
  */

import leon.lang._
import leon.annotation._
import leon.collection._
import leon.collection.ListOps._
import leon.lang.synthesis._

object ProblemRender {
  case class Identifier(name: String)
  sealed abstract class StringFormToken
  
  case class Left(e: String) extends StringFormToken
  case class Right(i: Identifier) extends StringFormToken
  
  type StringForm = List[StringFormToken]
  
  type Equation = (StringForm, String)
  
  /** Sequences of equalities such as xyz"1"uv"2" = "1, 2" */
  type Problem = List[Equation]
  
  /** Synthesis by example specs */
  @inline def psStandard(s: Problem) = (res: String) => (s, res) passes {
    case Cons((Cons(Left("1"), Cons(Right(Identifier("x")), Cons(Left("2"), Nil()))), "1432"),
         Cons((Cons(Right(Identifier("y")), Cons(Left("4"), Cons(Right(Identifier("y")), Nil()))), "141"), Nil())) => "\"1\"+x+\"2\"==1432, y+\"4\"+y==\"141\""
  }
  //////////////////////////////////////////////
  // Non-incremental examples: pure synthesis //
  //////////////////////////////////////////////
  def synthesizeStandard(s: List[Int]): String = {
    ???[String]
  } ensuring psStandard(s)

}