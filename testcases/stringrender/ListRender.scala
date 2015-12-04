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

object ListRender {
  /** Synthesis by example specs */
  @inline def psStandard(s: List[Int]) = (res: String) =>(s, res) passes {
    case Cons(12, Cons(-1, Nil())) => "Cons(12, Cons(-1, Nil))"
    case Cons(-1, Cons(12, Nil())) => "Cons(-1, Cons(12, Nil))"
    case Cons(1, Nil()) => "Cons(1, Nil)"
    case Nil() => "Nil"
  }
  
  @inline def psRemoveCons(s: List[Int]) = (res: String) =>(s, res) passes {
    case Cons(12, Cons(-1, Nil())) => "(12, (-1, Nil))"
    case Cons(1, Nil()) => "(1, Nil)"
    case Nil() => "Nil"
  }
  
  @inline def psRemoveNil(s: List[Int]) = (res: String) =>(s, res) passes {
    case Cons(12, Cons(-1, Nil())) => "(12, (-1, ))"
    case Cons(1, Nil()) => "(1, )"
    case Nil() => ""
  }
  
  @inline def psRemoveLastComma(s: List[Int]) = (res: String) =>(s, res) passes {
    case Cons(12, Cons(-1, Nil())) => "(12, (-1))"
    case Cons(1, Nil()) => "(1)"
    case Nil() => "()"
  }
  
  @inline def psRemoveParentheses(s: List[Int]) = (res: String) =>(s, res) passes {
    case Cons(12, Cons(-1, Nil())) => "12, -1"
    case Cons(1, Nil()) => "1"
    case Nil() => ""
  }
  
  @inline def psWrapParentheses(s: List[Int]) = (res: String) =>(s, res) passes {
    case Cons(12, Cons(-1, Nil())) => "(12, -1)"
  }
  
  @inline def psList(s: List[Int]) = (res: String) =>(s, res) passes {
    case Nil() => "List()"
    case Cons(1, Nil()) => "List(1)"
    case Cons(12, Cons(-1, Nil())) => "List(12, -1)"
  }

  /** Each function's body is the solution of the previous problem.
    * We want to check that the Leon can repair the programs and also find some ambiguities.*/
  def render1RemoveCons(s: List[Int]): String = {
    s match {
      case Nil() => "Nil"
      case Cons(a, b) => "Cons(" + a.toString + ", " + render1RemoveCons(b) + ")"
    }
  } ensuring psRemoveCons(s)
  
  def render2RemoveNil(s: List[Int]): String = {
    s match {
      case Nil() => "Nil"
      case Cons(a, b) => "(" + a.toString + ", " + render2RemoveNil(b) + ")"
    }
  } ensuring psRemoveNil(s)
  
  def render3RemoveLastComma(s: List[Int]): String = {
    s match {
      case Nil() => ""
      case Cons(a, b) => "(" + a.toString + ", " + render3RemoveLastComma(b) + ")"
    }
  } ensuring psRemoveLastComma(s)
  
  def render4RemoveParentheses(s: List[Int]): String = {
    s match {
      case Nil() => ""
      case Cons(a, Nil()) => "(" + a.toString +  ")"
      case Cons(a, b) => "(" + a.toString + ", " + render4RemoveParentheses(b) + ")"
    }
  } ensuring psRemoveParentheses(s)
  
  /* harder example: It needs to repair by wrapping the recursive call in a sub-method
   * in order to add strings to the left and to the right (see render6List) */
  def render5WrapParentheses(s: List[Int]): String = {
    s match {
      case Nil() => ""
      case Cons(a, Nil()) => a.toString
      case Cons(a, b) => a.toString + ", " + render5WrapParentheses(b)
    }
  } ensuring psWrapParentheses(s)
  
  def render6List(s: List[Int]): String = {
    def rec(s: List[Int]): String =
      s match {
        case Nil() => ""
        case Cons(a, Nil()) => a.toString
        case Cons(a, b) => a.toString + ", " + render6List(b)
      }
    "(" + rec(s) + ")"
  } ensuring psList(s)
  
  //////////////////////////////////////////////
  // Non-incremental examples: pure synthesis //
  //////////////////////////////////////////////
  def synthesizeStandard(s: List[Int]): String = {
    ???[String]
  } ensuring psStandard(s)

  def synthesizeRemoveCons(s: List[Int]): String = {
    ???[String]
  } ensuring psRemoveCons(s)
  
  def synthesizeRemoveNil(s: List[Int]): String = {
    ???[String]
  } ensuring psRemoveNil(s)
  
  def synthesizeRemoveLastComma(s: List[Int]): String = {
    ???[String]
  } ensuring psRemoveLastComma(s)
  
  def synthesizeRemoveParentheses(s: List[Int]): String = {
    ???[String]
  } ensuring psRemoveParentheses(s)
  
  def synthesizeWrapParentheses(s: List[Int]): String = {
    ???[String]
  } ensuring psWrapParentheses(s)
  
  def synthesizeList(s: List[Int]): String = {
    ???[String]
  } ensuring psList(s)
}