/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Types._

import utils._

case object CEGIS extends CEGISLike[TypeTree]("CEGIS") {
  def getParams(sctx: SynthesisContext, p: Problem) = {
    import ExpressionGrammars._
    CegisParams(
      grammar = depthBound(default(sctx, p), 2),
      rootLabel = {(tpe: TypeTree) => tpe }
    )
  }
}
