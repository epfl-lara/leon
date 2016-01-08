/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package utils

import purescala.Definitions._
import purescala.Types._
import purescala.DefOps._

case class Library(pgm: Program) {
  lazy val List = lookup("leon.collection.List").collectFirst { case acd : AbstractClassDef => acd }
  lazy val Cons = lookup("leon.collection.Cons").collectFirst { case ccd : CaseClassDef => ccd }
  lazy val Nil  = lookup("leon.collection.Nil").collectFirst { case ccd : CaseClassDef => ccd }

  lazy val Option = lookup("leon.lang.Option").collectFirst { case acd : AbstractClassDef => acd }
  lazy val Some   = lookup("leon.lang.Some").collectFirst { case ccd : CaseClassDef => ccd }
  lazy val None   = lookup("leon.lang.None").collectFirst { case ccd : CaseClassDef => ccd }

  //lazy val String = lookup("leon.lang.string.String").collectFirst { case ccd : CaseClassDef => ccd }
  lazy val StrOps = lookup("leon.lang.StrOps").collectFirst { case md: ModuleDef => md }

  lazy val Dummy  = lookup("leon.lang.Dummy").collectFirst { case ccd : CaseClassDef => ccd }

  lazy val setToList = lookup("leon.collection.setToList").collectFirst { case fd : FunDef => fd }
  
  lazy val escape = lookup("leon.lang.StrOps.escape").collectFirst { case fd : FunDef => fd }

  def lookup(name: String): Seq[Definition] = {
    pgm.lookupAll(name)
  }

  def optionType(tp: TypeTree) = AbstractClassType(Option.get, Seq(tp))
  def someType(tp: TypeTree) = CaseClassType(Some.get, Seq(tp))
  def noneType(tp: TypeTree) = CaseClassType(None.get, Seq(tp))
}
