/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Types._

import grammars._
import utils._

case object CEGIS extends CEGISLike[TypeTree]("CEGIS") {
  def getParams(sctx: SynthesisContext, p: Problem) = {
    CegisParams(
      grammar = Grammars.typeDepthBound(Grammars.default(sctx, p), 2), // This limits type depth
      rootLabel = {(tpe: TypeTree) => tpe }
    )
  }
}
