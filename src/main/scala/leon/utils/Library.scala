/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package utils

import purescala.Definitions._
import purescala.DefOps.searchByFullName

case class Library(pgm: Program) {
  lazy val List = lookup("leon.collection.List")
  lazy val Cons = lookup("leon.collection.Cons")
  lazy val Nil  = lookup("leon.collection.Nil")

  lazy val String = lookup("leon.lang.string.String")

  lazy val terminating: Option[FunDef] = lookup("leon.lang.synthesis.terminating").collect {
    case fd: FunDef => fd
  }

  lazy val passes = lookup("leon.lang.passes").collect {
    case fd: FunDef => fd
  }

  lazy val guide = lookup("leon.lang.synthesis.guide") collect {
    case (fd: FunDef) => fd
  }

  def lookup(name: String): Option[Definition] = {
    searchByFullName(name, pgm)
  }
}
