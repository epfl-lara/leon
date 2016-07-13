/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis

import leon.purescala.Definitions.FunDef

case class SynthesisSettings(
  timeoutMs: Option[Long]             = None,
  generateDerivationTrees: Boolean    = false,
  costModel: CostModel                = CostModels.default,
  rules: Seq[Rule]                    = Rules.all,
  manualSearch: Option[String]        = None,
  searchBound: Option[Int]            = None,
  functions: Option[Set[String]]      = None,
  functionsToIgnore: Set[FunDef]      = Set(),
  
  // STE related options
  steUseOptTimeout: Boolean = true,
  steUseVanuatoo  : Boolean = false,
  steMaxSize: Int           = 7

)
