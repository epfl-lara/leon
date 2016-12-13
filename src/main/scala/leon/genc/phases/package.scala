/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc

import purescala.Common.{ Identifier }
import purescala.Definitions.{ Definition, FunDef, ValDef, Program }
import purescala.Types.{ TypeTree }

/*
 * Some type aliased for readability
 */
package object phases {

  case class VarInfo(id: Identifier, typ: TypeTree, isVar: Boolean)

  type FunCtxDB = Map[FunDef, Seq[VarInfo]]

  case class Dependencies(prog: Program, deps: Set[Definition])

}

