/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis

import scala.language.existentials
import leon.purescala.Definitions.FunDef

case class SynthesisSettings(
  inPlace: Boolean                    = false,
  allSeeing: Boolean                  = false,
  generateDerivationTrees: Boolean    = false,
  filterFuns: Option[Set[String]]     = None,
  searchWorkers: Int                  = 1,
  firstOnly: Boolean                  = false,
  timeoutMs: Option[Long]             = None,
  costModel: CostModel                = CostModels.default,
  rules: Seq[Rule]                    = Rules.all,
  manualSearch: Option[String]        = None,
  searchBound: Option[Int]            = None,
  selectedSolvers: Set[String]        = Set("fairz3"),
  functionsToIgnore: Set[FunDef]      = Set(),
  
  // Cegis related options
  cegisUseOptTimeout: Option[Boolean] = None,
  cegisUseShrink: Option[Boolean]     = None,
  cegisUseVanuatoo: Option[Boolean]   = None,

  // Oracles and holes
  distreteHoles: Boolean              = false
)
