/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis

class BoundedSearch(synth: Synthesizer,
                   problem: Problem,
                   rules: Seq[Rule],
                   costModel: CostModel,
                   searchBound: Int) extends SimpleSearch(synth, problem, rules, costModel) {

  def this(synth: Synthesizer, problem: Problem, searchBound: Int) = {
    this(synth, problem, synth.rules, synth.options.costModel, searchBound)
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
