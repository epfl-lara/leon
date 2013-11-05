/* Copyright 2009-2013 EPFL, Lausanne */

package leon.test
package condabd

import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.solvers.z3._
import leon.solvers.Solver
import leon.synthesis._
import leon.synthesis.utils._

import org.scalatest.matchers.ShouldMatchers._

import synthesis.SynthesisSuite
import util._

import java.io.{BufferedWriter, FileWriter, File}

class SynthesizerTest extends SynthesisSuite {
  
  import Utils._
  import Scaffold._
 
  synthesize("List concat")("""
import leon.Utils._

object SortedList {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def size(l: List) : Int = (l match {
      case Nil() => 0
      case Cons(_, t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  def content(l: List): Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(i, t) => Set(i) ++ content(t)
  }

  def isSorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, Cons(y, ys)) => x <= y && isSorted(Cons(y, ys))
  }

  def concat(in1: List, in2: List) = choose {
    (out : List) =>
      content(out) == content(in1) ++ content(in2)
  }
}
    """) {
    case "concat" =>
      Apply("Condition abduction", List())
  } 
 
//  synthesize("Lists")("""
//import leon.Utils._
//
//object SortedList {
//  sealed abstract class List
//  case class Cons(head: Int, tail: List) extends List
//  case class Nil() extends List
//
//  def size(l: List) : Int = (l match {
//      case Nil() => 0
//      case Cons(_, t) => 1 + size(t)
//  }) ensuring(res => res >= 0)
//
//  def content(l: List): Set[Int] = l match {
//    case Nil() => Set.empty[Int]
//    case Cons(i, t) => Set(i) ++ content(t)
//  }
//
//  def isSorted(l: List): Boolean = l match {
//    case Nil() => true
//    case Cons(x, Nil()) => true
//    case Cons(x, Cons(y, ys)) => x <= y && isSorted(Cons(y, ys))
//  }
//
//  def concat(in1: List, in2: List) = choose {
//    (out : List) =>
//      content(out) == content(in1) ++ content(in2)
//  }
//
//  def insert(in1: List, v: Int) = choose {
//    (out : List) =>
//      content(out) == content(in1) ++ Set(v)
//  }
//
//  def insertSorted(in1: List, v: Int) = choose {
//    (out : List) =>
//      isSorted(in1) && content(out) == content(in1) ++ Set(v) && isSorted(out)
//  }
//}
//    """) {
//    case "concat" =>
//      Apply("Condition abduction", List())
//    case "insert" =>
//      Apply("Condition abduction", List())
//    case "insertSorted" =>
//      Apply("Condition abduction", List())
//  }
}