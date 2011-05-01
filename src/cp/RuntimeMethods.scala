package cp

/** A collection of methods that are called on runtime */
object RuntimeMethods {
  import Serialization._
  import Constraints._
  import Definitions.UnsatisfiableConstraintException
  import Definitions.UnknownConstraintException
  import purescala.Definitions._
  import purescala.Trees._
  import purescala.Common._
  import purescala.{DefaultReporter,QuietReporter}
  import purescala.FairZ3Solver

  import purescala.Stopwatch
  
  /* WILL BE PORTED TO Constraints.scala
  private def chooseMaximizingExec(program : Program, expr : Expr, outputVars : Seq[Identifier], maxExpr : Expr, inputConstraints : Expr) : Seq[Expr] = {
    def stop(lo : Int, hi : Option[Int]) : Boolean = hi match {
      case Some(h) => h - lo <= 2
      case None => false
    }

    val solver = newSolver()
    solver.setProgram(program)

    // invariant : hi is always strictly greater than any sat. maxExpr assignment,
    // and there is always a sat. assignment >= lo 
    def maxAux(pivot : Int, lo : Int, hi : Option[Int]) : Map[Identifier, Expr] = {
      // println("Iterating:")
      // println("  lo     : " + lo)
      // println("  pivot  : " + pivot)
      // println("  hi     : " + (hi match { case Some(h) => h; case None => "+inf"}))
      // println
      val toCheck = expr :: inputConstraints :: GreaterEquals(maxExpr, IntLiteral(pivot)) :: Nil
      val (outcome, model) = solver.restartAndDecideWithModel(And(toCheck), false)

      outcome match {
        case Some(false) =>
          // there is a satisfying assignment
          if (stop(lo, hi)) {
            model
          } else {
            hi match {
              case None =>
                // upper bound is +inf
                maxAux(
                  if (pivot <= 0) 1 else pivot * 2,
                  pivot,
                  None
                )
              case Some(hv) =>
                maxAux(
                  pivot + (hv - pivot) / 2,
                  pivot,
                  hi
                )
            }
          }
        case _ =>
          // new hi is pivot
          maxAux(
            lo + (pivot - lo) / 2,
            lo,
            Some(pivot)
          )
      }
    }

    val maxExprID = purescala.Common.FreshIdentifier("maxExpr").setType(purescala.TypeTrees.Int32Type)

    solver.restartAndDecideWithModel(And(expr :: inputConstraints :: Equals(maxExpr, Variable(maxExprID)) :: Nil), false) match {
      case (Some(false), model) =>
        // there is a satisfying assignment
        val maxExprVal = modelValue(maxExprID, model) match {
          case IntLiteral(i) => i
          case e => scala.Predef.error("Unexpected value for term to maximize : " + e)
        }

        val optimalModel = maxAux(maxExprVal, maxExprVal - 1, None)
        outputVars.map(v => modelValue(v, optimalModel))
      case (Some(true),_) =>
        throw new UnsatisfiableConstraintException()
      case _ =>
        throw new UnknownConstraintException()
    }
  }
  */

  def skipCounter(i : Int) : Unit = {
    purescala.Common.FreshIdentifier.forceSkip(i)
  }

  def copySettings(serializedSettings : Serialized) : Unit = {
    val recovered = deserialize[RuntimeSettings](serializedSettings)
  
    purescala.Settings.experimental         = recovered.experimental
    purescala.Settings.showIDs              = recovered.showIDs
    purescala.Settings.noForallAxioms       = recovered.noForallAxioms
    purescala.Settings.unrollingLevel       = recovered.unrollingLevel
    purescala.Settings.zeroInlining         = recovered.zeroInlining
    purescala.Settings.useBAPA              = recovered.useBAPA
    purescala.Settings.useInstantiator      = recovered.useInstantiator
    purescala.Settings.useFairInstantiator  = recovered.useFairInstantiator
    purescala.Settings.useCores             = recovered.useCores
    purescala.Settings.pruneBranches        = recovered.pruneBranches
    purescala.Settings.solverTimeout        = recovered.solverTimeout
  }
  
  def inputVar(inputVarList : List[Variable], varName : String) : Variable = {
    inputVarList.find(_.id.name == varName).getOrElse(scala.Predef.error("Could not find input variable '" + varName + "' in list " + inputVarList))
  }
}
