/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

class BoundedSearch(synth: Synthesizer,
                   problem: Problem,
                   costModel: CostModel,
                   searchBound: Int) extends SimpleSearch(synth, problem, costModel) {

  def this(synth: Synthesizer, problem: Problem, searchBound: Int) = {
    this(synth, problem, synth.options.costModel, searchBound)
  }

  override def searchStep() {
    val (closed, total) = g.getStatus
    if (total > searchBound) {
      stop()
    } else {
      super.searchStep()
    }
  }
}
