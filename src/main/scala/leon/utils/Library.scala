/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package utils

import purescala.Definitions._
import purescala.DefOps.searchByFullName

case class Library(pgm: Program) {
  lazy val List = lookup("leon.collection.List") collect { case acd : AbstractClassDef => acd }
  lazy val Cons = lookup("leon.collection.Cons") collect { case ccd : CaseClassDef => ccd }
  lazy val Nil  = lookup("leon.collection.Nil") collect { case ccd : CaseClassDef => ccd }

  lazy val String = lookup("leon.lang.string.String") collect { case ccd : CaseClassDef => ccd }
  
  def lookup(name: String): Option[Definition] = {
    searchByFullName(name, pgm)
  }
}
