/**
  * Name:     IntWrapperRender.scala
  * Creation: 15.10.2015
  * Author:   Mikaël Mayer (mikael.mayer@epfl.ch)
  * Comments: Wrapped integer specifications.
  */

import leon.lang._
import leon.annotation._
import leon.collection._
import leon.collection.ListOps._
import leon.lang.synthesis._

object IntWrapperRender {
  case class IntWrapper(i: Int)

  @inline def psStandard(s: IntWrapper) = (res: String) => (s, res) passes {
    case IntWrapper(0) => "IntWrapper(0)"
    case IntWrapper(-1) => "IntWrapper(-1)"
    case IntWrapper(12) => "IntWrapper(12)"
  }
  
  @inline def psUnwrapped(s: IntWrapper) = (res: String) => (s, res) passes {
    case IntWrapper(0) => "0"
    case IntWrapper(-1) => "-1"
    case IntWrapper(12) => "12"
  }
  
  @inline def psNameChangedPrefix(s: IntWrapper) = (res: String) => (s, res) passes {
    case IntWrapper(0) => "number: 0"
    case IntWrapper(-1) => "number: -1"
    case IntWrapper(12) => "number: 12"
  }
  
  @inline def psNameChangedSuffix(s: IntWrapper) = (res: String) => (s, res) passes {
    case IntWrapper(0) => "0.0"
    case IntWrapper(-1) => "-1.0" // Here there should be an ambiguity before this line.
    case IntWrapper(12) => "12.0"
  }
  
  /*@inline def psDuplicate(s: IntWrapper) = (res: String) => (s, res) passes {
    case IntWrapper(0) => "0 0"
    case IntWrapper(-1) => "-1 -1"
    case IntWrapper(12) => "12 12"
  }*/
  
  def repairUnwrapped(s: IntWrapper): String = {
    "IntWrapper(" + s.i + ")"
  } ensuring psUnwrapped(s)
  
  def repairNameChangedPrefix(s: IntWrapper): String = {
    "IntWrapper(" + s.i + ")"
  } ensuring psNameChangedPrefix(s)
  
  def repairNameChangedSuffix(s: IntWrapper): String = {
    "IntWrapper(" + s.i + ")"
  } ensuring psNameChangedSuffix(s)
  
  /*def repairDuplicate(s: IntWrapper): String = {
    "IntWrapper(" + s.i + ")"
  } ensuring psDuplicate(s)*/
  
  def synthesizeStandard(s: IntWrapper): String = {
     ???[String]
  } ensuring psStandard(s)
  
  def synthesizeUnwrapped(s: IntWrapper): String = {
     ???[String]
  } ensuring psUnwrapped(s)
  
  def synthesizeNameChangedPrefix(s: IntWrapper): String = {
     ???[String]
  } ensuring psNameChangedPrefix(s)
  
  def synthesizeNameChangedSuffix(s: IntWrapper): String = {
     ???[String]
  } ensuring psNameChangedSuffix(s)
  
  /*def synthesizeDuplicate(s: IntWrapper): String = {
     ???[String]
  } ensuring psDuplicate(s)*/
}