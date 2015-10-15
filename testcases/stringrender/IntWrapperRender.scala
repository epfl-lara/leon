/**
  * Name:     IntWrapperRender.scala
  * Creation: 15.10.2015
  * Author:   Mikaël Mayer (mikael.mayer@epfl.ch)
  * Comments: First benchmark ever for solving string transformation problems. List specifications.
  */

import leon.lang._
import leon.annotation._
import leon.collection._
import leon.collection.ListOps._
import leon.lang.synthesis._

object IntWrapperRender {
  case class IntWrapper(i: Int)

  def psStandard(s: IntWrapper)(res: String) = (s, res) passes {
    case IntWrapper(0) => "IntWrapper(0)"
    case IntWrapper(-1) => "IntWrapper(-1)"
    case IntWrapper(12) => "IntWrapper(12)"
  }
  
  def psUnwrapped(s: IntWrapper)(res: String) = (s, res) passes {
    case IntWrapper(0) => "0"
    case IntWrapper(-1) => "-1"
    case IntWrapper(12) => "12"
  }
  
  def psNameChangedPrefix(s: IntWrapper)(res: String) = (s, res) passes {
    case IntWrapper(0) => "number: 0"
    case IntWrapper(-1) => "number: -1"
    case IntWrapper(12) => "number: 12"
  }
  
  def psNameChangedSuffix(s: IntWrapper)(res: String) = (s, res) passes {
    case IntWrapper(0) => "0.0"
    case IntWrapper(-1) => "-1.0" // Here there should be an ambiguity before this line.
    case IntWrapper(12) => "12.0"
  }
  
  def psDuplicate(s: IntWrapper)(res: String) = (s, res) passes {
    case IntWrapper(0) => "0 0"
    case IntWrapper(-1) => "-1 -1"
    case IntWrapper(12) => "12 12"
  }
  
  def synthesisStandard(s: IntWrapper): String = {
     ???[String]
  } ensuring psStandard(s)
  
  def synthesisUnwrapped(s: IntWrapper): String = {
     ???[String]
  } ensuring psUnwrapped(s)
  
  def synthesisNameChangedPrefix(s: IntWrapper): String = {
     ???[String]
  } ensuring psNameChangedPrefix(s)
  
  def synthesisNameChangedSuffix(s: IntWrapper): String = {
     ???[String]
  } ensuring psNameChangedSuffix(s)
  
  def synthesisDuplicate(s: IntWrapper): String = {
     ???[String]
  } ensuring psDuplicate(s)
}