/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package utils

import purescala.Definitions._
import purescala.TypeTrees._
import purescala.TypeTreeOps._
import purescala.Trees._

object Helpers {
  def functionsReturning(fds: Set[FunDef], tpe: TypeTree): Set[TypedFunDef] = {
    fds.flatMap { fd =>
      val free = fd.tparams.map(_.tp)
      canBeSubtypeOf(fd.returnType, free, tpe) match {
        case Some(tpsMap) =>
          Some(fd.typed(free.map(tp => tpsMap.getOrElse(tp, tp))))
        case None =>
          None
      }
    }
  }

  def definitionsAvailable(p: Program, from: Definition): Set[Definition] = {
    Set()
  }

  def functionsAvailable(p: Program, from: Definition): Set[FunDef] = {
    definitionsAvailable(p, from).collect {
      case fd: FunDef => fd
    }
  }
}
