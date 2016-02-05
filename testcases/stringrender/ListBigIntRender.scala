/** 
  * Name:     ListBigIntRender.scala
  * Creation: 15.10.2015
  * Author:   Mika�l Mayer (mikael.mayer@epfl.ch)
  * Comments: List of BigInt specifications.
  */

import leon.lang._
import leon.annotation._
import leon.collection._
import leon.collection.ListOps._
import leon.lang.synthesis._

object ListBigIntRender {
  /** Synthesis by example specs */
  @inline def psWithBigInts(s: List[BigInt]) = (res: String) => (s, res) passes {
    case Cons(BigInt(12), Cons(BigInt(-1), Nil())) => "Cons(BigInt(12), Cons(BigInt(-1), Nil()))"
    case Cons(BigInt(1), Nil()) => "Cons(BigInt(1), Nil())"
    case Nil() => "Nil()"
  }
  
  @inline def psStandard(s: List[BigInt]) = (res: String) => (s, res) passes {
    case Cons(BigInt(12), Cons(BigInt(-1), Nil())) => "Cons(12, Cons(-1, Nil()))"
    case Cons(BigInt(1), Nil()) => "Cons(1, Nil())"
    case Nil() => "Nil()"
  }
  
  @inline def psRemoveCons(s: List[BigInt]) = (res: String) => (s, res) passes {
    case Cons(BigInt(12), Cons(BigInt(-1), Nil())) => "(12, (-1, Nil()))"
    case Cons(BigInt(1), Nil()) => "(1, Nil())"
    case Nil() => "Nil()"
  }
  
  @inline def psRemoveNil(s: List[BigInt]) = (res: String) => (s, res) passes {
    case Cons(BigInt(12), Cons(BigInt(-1), Nil())) => "(12, (-1, ))"
    case Cons(BigInt(1), Nil()) => "(1, )"
    case Nil() => ""
  }
  
  @inline def psRemoveLastComma(s: List[BigInt]) = (res: String) => (s, res) passes {
    case Cons(BigInt(12), Cons(BigInt(-1), Nil())) => "(12, (-1))"
    case Cons(BigInt(1), Nil()) => "(1)"
    case Nil() => "()"
  }
  
  @inline def psRemoveParentheses(s: List[BigInt]) = (res: String) => (s, res) passes {
    case Cons(BigInt(12), Cons(BigInt(-1), Nil())) => "12, -1"
    case Cons(BigInt(1), Nil()) => "1"
    case Nil() => ""
  }
  
  @inline def psWrapParentheses(s: List[BigInt]) = (res: String) => (s, res) passes {
    case Cons(BigInt(12), Cons(BigInt(-1), Nil())) => "(12, -1)"
    case Cons(BigInt(1), Nil()) => "(1)"
    case Nil() => "()"
  }
  
  @inline def psList(s: List[BigInt]) = (res: String) => (s, res) passes {
    case Nil() => "List()"
    case Cons(BigInt(1), Nil()) => "List(1)"
    case Cons(BigInt(12), Cons(BigInt(-1), Nil())) => "List(12, -1)"
  }

  /** Each function's body is the solution of the previous problem.
    * We want to check that the Leon can repair the programs and also find some ambiguities.*/
  /*def render0RemoveBigInt(s: List[BigInt]): String = {
    def renderBigInt(b: BigInt): String = {
      b.toString()
    }
    s match {
      case Nil() => "Nil()"
      case Cons(a, b) => "Cons(" + renderBigInt(a) + ", " + render1RemoveCons(b) + ")"
    }
  } ensuring psRemoveCons(s)
  
  def render1RemoveCons(s: List[BigInt]): String = {
    def renderBigInt(b: BigInt): String = {
      val a  = b.toString()
      a.substring(6, a.length - 1)
    }
    s match {
      case Nil() => "Nil()"
      case Cons(a, b) => "Cons(" + renderBigInt(a) + ", " + render1RemoveCons(b) + ")"
    }
  } ensuring psRemoveCons(s)
  
  def render2RemoveNil(s: List[BigInt]): String = {
    def renderBigInt(b: BigInt): String = {
      val a  = b.toString()
      a.substring(6, a.length - 1)
    }
    s match {
      case Nil() => "Nil()"
      case Cons(a, b) => "(" + renderBigInt(a) + ", " + render2RemoveNil(b) + ")"
    }
  } ensuring psRemoveNil(s)
  
  def render3RemoveLastComma(s: List[BigInt]): String = {
    def renderBigInt(b: BigInt): String = {
      val a  = b.toString()
      a.substring(6, a.length - 1)
    }
    s match {
      case Nil() => ""
      case Cons(a, b) => "(" + renderBigInt(a) + ", " + render3RemoveLastComma(b) + ")"
    }
  } ensuring psRemoveLastComma(s)
  
  def render4RemoveParentheses(s: List[BigInt]): String = {
    def renderBigInt(b: BigInt): String = {
      val a  = b.toString()
      a.substring(6, a.length - 1)
    }
    s match {
      case Nil() => ""
      case Cons(a, Nil()) => "(" + renderBigInt(a) +  ")"
      case Cons(a, b) => "(" + renderBigInt(a) + ", " + render4RemoveParentheses(b) + ")"
    }
  } ensuring psRemoveParentheses(s)*/
  
  /* harder example: It needs to repair by wrapping the recursive call in a sub-method
   * in order to add strings to the left and to the right (see render6List) */
  /*def render5WrapParentheses(s: List[BigInt]): String = {
    def renderBigInt(b: BigInt): String = {
      val a  = b.toString()
      a.substring(6, a.length - 1)
    }
    s match {
      case Nil() => ""
      case Cons(a, Nil()) => renderBigInt(a)
      case Cons(a, b) => renderBigInt(a) + ", " + render5WrapParentheses(b)
    }
  } ensuring psWrapParentheses(s)
  
  def render6List(s: List[BigInt]): String = {
    def renderBigInt(b: BigInt): String = {
      val a  = b.toString()
      a.substring(6, a.length - 1)
    }
    def rec(s: List[BigInt]): String =
      s match {
        case Nil() => ""
        case Cons(a, Nil()) => renderBigInt(a)
        case Cons(a, b) => renderBigInt(a) + ", " + render6List(b)
      }
    "(" + rec(s) + ")"
  } ensuring psList(s)*/
  
  //////////////////////////////////////////////
  // Non-incremental examples: pure synthesis //
  //////////////////////////////////////////////
  def synthesizeStandard(s: List[BigInt]): String = {
    ???[String]
  } ensuring psStandard(s)
  
  def synthesizeWithBigInts(s: List[BigInt]): String = {
    ???[String]
  } ensuring psWithBigInts(s)

  def synthesizeRemoveCons(s: List[BigInt]): String = {
    ???[String]
  } ensuring psRemoveCons(s)
  
  def synthesizeRemoveNil(s: List[BigInt]): String = {
    ???[String]
  } ensuring psRemoveNil(s)
  
  def synthesizeRemoveLastComma(s: List[BigInt]): String = {
    ???[String]
  } ensuring psRemoveLastComma(s)
  
  def synthesizeRemoveParentheses(s: List[BigInt]): String = {
    ???[String]
  } ensuring psRemoveParentheses(s)
  
  def synthesizeWrapParentheses(s: List[BigInt]): String = {
    ???[String]
  } ensuring psWrapParentheses(s)
  
  def synthesizeList(s: List[BigInt]): String = {
    ???[String]
  } ensuring psList(s)
}