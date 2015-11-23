/**
  * Name:     TupleWrapperRender.scala
  * Creation: 15.10.2015
  * Author:   Mikaël Mayer (mikael.mayer@epfl.ch)
  * Comments: Tuple rendering specifications.
  */

import leon.annotation._
import leon.collection._
import leon.collection.ListOps._
import leon.lang.synthesis._
import leon.lang._

object TwoArgsWrapperRender {
  @inline def psStandard(s: Int, t: Int) = (res: String) => ((s, t), res) passes {
    case (0, 0) => "TupleWrapper(0, 0)"
    case (-1, 2) => "TupleWrapper(-1, 2)"
    case (12, 5) => "TupleWrapper(12, 5)"
  }
  
  @inline def psUnwrapped(s: Int, t: Int) = (res: String) => ((s, t), res) passes {
    case (0, 0) => "0, 0"
    case (-1, 2) => "-1, 2"
    case (12, 5) => "12, 5"
  }
  
  @inline def psNameChangedPrefix(s: Int, t: Int) = (res: String) => ((s, t), res) passes {
    case (0, 0) => "x = 0, y = 0"
    case (-1, 2) => "x = -1, y = 2"
    case (12, 5) => "x = 12, y = 5"
  }
  
  @inline def psNameChangedSuffix(s: Int, t: Int) = (res: String) => ((s, t), res) passes {
    case (0, 0) => "0.0,0.0"
    case (-1, 2) => "-1.0,2.0" // Here there should be an ambiguity before this line.
    case (12, 5) => "12.0,5.0"
  }
  
  /*def psDuplicate(s: Int, t: Int) = (res: String) => ((s, t), res) passes {
    case (0, 0) => "d 0,0 0,15 15,15 15,0"
    case (-1, 2) => "d -1,-2 -1,15 15,15 15,2"
    case (12, 5) => "d 12,5 12,15 15,15 15,5"
  }*/
  
  def repairUnWrapped(s: Int, t: Int): String = {
    "(" + s + ", " + t + ")"
  } ensuring psUnwrapped(s, t)
  
  def repairNameChangedPrefix(s: Int, t: Int): String = {
    "(" + s + ", " + t + ")"
  } ensuring psNameChangedPrefix(s, t)
  
  def repairNameChangedSuffix(s: Int, t: Int): String = {
    "(" + s + ", " + t + ")"
  } ensuring psNameChangedSuffix(s, t)
  
  /*def repairDuplicate(s: Int, t: Int): String = {
    "(" + s + ", " + t + ")"
  } ensuring psDuplicate(s)*/
  
  
  def synthesizeStandard(s: Int, t: Int): String = {
     ???[String]
  } ensuring psStandard(s, t)
  
  def synthesizeUnwrapped(s: Int, t: Int): String = {
     ???[String]
  } ensuring psUnwrapped(s, t)
  
  def synthesizeNameChangedPrefix(s: Int, t: Int): String = {
     ???[String]
  } ensuring psNameChangedPrefix(s, t)
  
  def synthesizeNameChangedSuffix(s: Int, t: Int): String = {
     ???[String]
  } ensuring psNameChangedSuffix(s, t)
  
  /*def synthesizeDuplicate(s: Int, t: Int): String = {
     ???[String]
  } ensuring psDuplicate(s)*/
}