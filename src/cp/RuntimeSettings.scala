package cp

@serializable class RuntimeSettings {
  var experimental : Boolean = purescala.Settings.experimental 
  var showIDs: Boolean = purescala.Settings.showIDs
  var noForallAxioms: Boolean = purescala.Settings.noForallAxioms
  var unrollingLevel: Int = purescala.Settings.unrollingLevel
  var zeroInlining : Boolean = purescala.Settings.zeroInlining 
  var useBAPA: Boolean = purescala.Settings.useBAPA
  var useInstantiator: Boolean = purescala.Settings.useInstantiator
  var useFairInstantiator: Boolean = purescala.Settings.useFairInstantiator
  var useCores : Boolean = purescala.Settings.useCores 
  var pruneBranches : Boolean = purescala.Settings.pruneBranches 
  var solverTimeout : Option[Int] = purescala.Settings.solverTimeout 
  var luckyTest : Boolean = purescala.Settings.luckyTest 

  var useScalaEvaluator : Boolean = Settings.useScalaEvaluator
  var verbose : Boolean = Settings.verbose
}

object Settings {
  var useScalaEvaluator : Boolean = false
  var verbose : Boolean = false
}
