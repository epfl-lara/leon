/**
  * Name:     TupleWrapperRender.scala
  * Creation: 15.10.2015
  * Author:   Mikaël Mayer (mikael.mayer@epfl.ch)
  * Comments: Tuple rendering specifications.
  */

import leon.lang._
import string.String
import leon.annotation._
import leon.collection._
import leon.collection.ListOps._
import leon.lang.synthesis._

object TupleWrapperRender {
  case class TupleWrapper(i: Int, j: Int)

  def psStandard(s: TupleWrapper)(res: String) = (s, res) passes {
    case TupleWrapper(0, 0) => "TupleWrapper(0, 0)"
    case TupleWrapper(-1, 2) => "TupleWrapper(-1, 2)"
    case TupleWrapper(12, 5) => "TupleWrapper(12, 5)"
  }
  
  def psUnwrapped(s: TupleWrapper)(res: String) = (s, res) passes {
    case TupleWrapper(0, 0) => "0, 0"
    case TupleWrapper(-1, 2) => "-1, 2"
    case TupleWrapper(12, 5) => "(12, 5)"
  }
  
  def psNameChangedPrefix(s: TupleWrapper)(res: String) = (s, res) passes {
    case TupleWrapper(0, 0) => "x = 0, y = 0"
    case TupleWrapper(-1, 2) => "x = -1, y = 2"
    case TupleWrapper(12, 5) => "x = 12, y = 5"
  }
  
  def psNameChangedSuffix(s: TupleWrapper)(res: String) = (s, res) passes {
    case TupleWrapper(0, 0) => "0.0,0.0"
    case TupleWrapper(-1, 2) => "-1.0,2.0" // Here there should be an ambiguity before this line.
    case TupleWrapper(12, 5) => "12.0,5.0"
  }
  
  def psDuplicate(s: TupleWrapper)(res: String) = (s, res) passes {
    case TupleWrapper(0, 0) => "d 0,0 0,15 15,15 15,0"
    case TupleWrapper(-1, 2) => "d -1,-2 -1,15 15,15 15,2"
    case TupleWrapper(12, 5) => "d 12,5 12,15 15,15 15,5"
  }
  
  def repairUnWrapped(s: IntWrapper): String = {
    "TupleWrapper(" + s.i + ", " + s.j + ")""
  } ensuring psUnWrapped(s)
  
  def repairNameChangedPrefix(s: IntWrapper): String = {
    "TupleWrapper(" + s.i + ", " + s.j + ")""
  } ensuring psNameChangedPrefix(s)
  
  def repairNameChangedSuffix(s: IntWrapper): String = {
    "TupleWrapper(" + s.i + ", " + s.j + ")""
  } ensuring psNameChangedSuffix(s)
  
  def repairDuplicate(s: IntWrapper): String = {
    "TupleWrapper(" + s.i + ", " + s.j + ")""
  } ensuring psDuplicate(s)
  
  
  def synthesisStandard(s: TupleWrapper): String = {
     ???[String]
  } ensuring psStandard(s)
  
  def synthesisUnwrapped(s: TupleWrapper): String = {
     ???[String]
  } ensuring psUnwrapped(s)
  
  def synthesisNameChangedPrefix(s: TupleWrapper): String = {
     ???[String]
  } ensuring psNameChangedPrefix(s)
  
  def synthesisNameChangedSuffix(s: TupleWrapper): String = {
     ???[String]
  } ensuring psNameChangedSuffix(s)
  
  def synthesisDuplicate(s: TupleWrapper): String = {
     ???[String]
  } ensuring psDuplicate(s)
}