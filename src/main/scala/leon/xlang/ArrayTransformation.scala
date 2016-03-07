/* Copyright 2009-2016 EPFL, Lausanne */

package leon.xlang

import leon.UnitPhase
import leon.LeonContext
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.ExprOps.simplePostTransform
import leon.purescala.Extractors.IsTyped
import leon.purescala.Types.ArrayType
import leon.xlang.Expressions._

object ArrayTransformation extends UnitPhase[Program] {

  val name = "Array Transformation"
  val description = "Remove side-effectful array updates"

  def apply(ctx: LeonContext, pgm: Program) = {
    pgm.definedFunctions.foreach(fd =>
      fd.fullBody = simplePostTransform {
        case up@ArrayUpdate(a, i, v) =>
          val ra@Variable(id) = a
          Assignment(id, ArrayUpdated(ra, i, v).setPos(up)).setPos(up)

        case l@Let(i, IsTyped(v, ArrayType(_)), b) =>
          LetVar(i, v, b).setPos(l)

        case e =>
          e
      }(fd.fullBody)
    )
  }

}
