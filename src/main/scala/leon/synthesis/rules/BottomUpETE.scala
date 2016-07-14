/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

case object BottomUpETE extends BottomUpETELike("BU Example-guided Term Exploration") {
  def getParams(sctx: SynthesisContext, p: Problem) = {
    ETEParams(
      grammar = grammars.default(sctx, p),
      maxExpands = 4
    )
  }
}
