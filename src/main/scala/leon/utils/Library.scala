/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package utils

import purescala.Definitions._
import purescala.Types._
import purescala.DefOps.searchByFullName

case class Library(pgm: Program) {
  lazy val List = lookup("leon.collection.List") collect { case acd : AbstractClassDef => acd }
  lazy val Cons = lookup("leon.collection.Cons") collect { case ccd : CaseClassDef => ccd }
  lazy val Nil  = lookup("leon.collection.Nil") collect { case ccd : CaseClassDef => ccd }

  lazy val Option = lookup("leon.lang.Option") collect { case acd : AbstractClassDef => acd }
  lazy val Some = lookup("leon.lang.Some") collect { case ccd : CaseClassDef => ccd }
  lazy val None = lookup("leon.lang.None") collect { case ccd : CaseClassDef => ccd }

  lazy val String = lookup("leon.lang.string.String") collect { case ccd : CaseClassDef => ccd }

  lazy val setToList = lookup("leon.collection.setToList") collect { case fd : FunDef => fd }
  
  def lookup(name: String): Option[Definition] = {
    searchByFullName(name, pgm)
  }

  def optionType(tp: TypeTree) = AbstractClassType(Option.get, Seq(tp))
  def someType(tp: TypeTree) = CaseClassType(Some.get, Seq(tp))
  def noneType(tp: TypeTree) = CaseClassType(None.get, Seq(tp))
}
