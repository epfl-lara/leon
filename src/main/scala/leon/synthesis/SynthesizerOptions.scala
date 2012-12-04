package leon
package synthesis

case class SynthesizerOptions(
  generateDerivationTrees: Boolean = false,
  filterFuns: Option[Set[String]]  = None,
  parallel: Boolean                = false,
  firstOnly: Boolean               = false,
  timeoutMs: Option[Long]          = None,
  costModel: CostModel             = NaiveCostModel
)
