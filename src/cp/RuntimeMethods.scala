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
  
  private val silent = true
  private def newReporter() = if (silent) new QuietReporter() else new DefaultReporter()
  private def newSolver() = new FairZ3Solver(newReporter())

  def chooseExec(serializedProg : Serialized, serializedConstraint : Serialized) : Seq[Expr] = {
    val program    = deserialize[Program](serializedProg)
    val constraint = deserialize[Constraint](serializedConstraint)

    chooseExec(program, constraint)
  }

  private def chooseExec(program : Program, constraint : Constraint) : Seq[Expr] = {
    val solver = newSolver()
    solver.setProgram(program)

    throw new Exception("not implemented")
    /*
    val toCheck = expr :: inputConstraints :: Nil
    val (outcome, model) = solver.restartAndDecideWithModel(And(toCheck), false)

    outcome match {
      case Some(false) =>
        outputVars.map(v => modelValue(v, model))
      case Some(true) =>
        throw new UnsatisfiableConstraintException()
      case None =>
        throw new UnknownConstraintException()
    }
    */
  }

  def chooseMinimizingExec(serializedProg : Serialized, serializedExpr : Serialized, serializedOutputVars : Serialized, serializedMinExpr : Serialized, inputConstraints : Expr) : Seq[Expr] = {
    val program    = deserialize[Program](serializedProg)
    val expr       = deserialize[Expr](serializedExpr)
    val outputVars = deserialize[Seq[Identifier]](serializedOutputVars)
    val minExpr    = deserialize[Expr](serializedMinExpr)

    chooseMinimizingExec(program, expr, outputVars, minExpr, inputConstraints)
  }

  private def chooseMinimizingExec(program : Program, expr : Expr, outputVars : Seq[Identifier], minExpr : Expr, inputConstraints : Expr) : Seq[Expr] = {
    chooseMinimizingModelAndValue(program, expr, outputVars, minExpr, inputConstraints)._1
  }

  private def chooseMinimizingModelAndValue(program : Program, expr : Expr, outputVars : Seq[Identifier], minExpr : Expr, inputConstraints : Expr) : (Seq[Expr], Int) = {
    def stop(lo : Option[Int], hi : Int) : Boolean = lo match {
      case Some(l) => hi - l <= 2
      case None => false
    }
    
    val solver = newSolver()
    solver.setProgram(program)

    /* invariant : lo is always stricly less than any sat. minExpr assignment,
     * and there is always a sat. assignment less than hi */
    def minAux(pivot : Int, lo : Option[Int], hi : Int) : (Map[Identifier, Expr], Int) = {
      // println("Iterating:")
      // println("  lo     : " + (lo match { case Some(l) => l; case None => "-inf"}))
      // println("  pivot  : " + pivot)
      // println("  hi     : " + hi)
      // println
      val toCheck = expr :: inputConstraints :: LessEquals(minExpr, IntLiteral(pivot)) :: Nil
      val (outcome, model) = solver.restartAndDecideWithModel(And(toCheck), false)

      outcome match {
        case Some(false) =>
          // there is a satisfying assignment
          if (stop(lo, hi)) {
            (model, pivot)
          } else {
            lo match {
              case None =>
                // lower bound is -inf
                minAux(
                  if (pivot >= 0) -1 else pivot * 2,
                  None,
                  pivot + 1
                )
              case Some(lv) =>
                minAux(
                  lv + (pivot + 1 - lv) / 2,
                  lo,
                  pivot + 1
                )
            }
          }
        case _ =>
          // new lo is pivot
          minAux(
            pivot + (hi - pivot) / 2,
            Some(pivot),
            hi
          )
      }
    }

    // We declare a variable to hold the value to minimize:
    val minExprID = purescala.Common.FreshIdentifier("minExpr").setType(purescala.TypeTrees.Int32Type)

    solver.restartAndDecideWithModel(And(expr :: inputConstraints :: Equals(minExpr, Variable(minExprID)) :: Nil), false) match {
      case (Some(false), model) =>
        // there is a satisfying assignment
        val minExprVal = modelValue(minExprID, model) match {
          case IntLiteral(i) => i
          case e => scala.Predef.error("Unexpected value for term to minimize : " + e)
        }

        val (optimalModel, optimalValue) = minAux(minExprVal - 1, None, minExprVal + 1)
        (outputVars.map(v => modelValue(v, optimalModel)), optimalValue)
      case (Some(true), _) =>
        throw new UnsatisfiableConstraintException()
      case _ =>
        throw new UnknownConstraintException()
    }
  }

  def chooseMaximizingExec(serializedProg : Serialized, serializedExpr : Serialized, serializedOutputVars : Serialized, serializedMaxExpr : Serialized, inputConstraints : Expr) : Seq[Expr] = {
    val program    = deserialize[Program](serializedProg)
    val expr       = deserialize[Expr](serializedExpr)
    val outputVars = deserialize[Seq[Identifier]](serializedOutputVars)
    val maxExpr    = deserialize[Expr](serializedMaxExpr)

    chooseMaximizingExec(program, expr, outputVars, maxExpr, inputConstraints)
  }
   
  private def chooseMaximizingExec(program : Program, expr : Expr, outputVars : Seq[Identifier], maxExpr : Expr, inputConstraints : Expr) : Seq[Expr] = {
    def stop(lo : Int, hi : Option[Int]) : Boolean = hi match {
      case Some(h) => h - lo <= 2
      case None => false
    }

    val solver = newSolver()
    solver.setProgram(program)

    /* invariant : hi is always strictly greater than any sat. maxExpr assignment,
     * and there is always a sat. assignment >= lo */
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

  def findExec(serializedProg : Serialized, serializedExpr : Serialized, serializedOutputVars : Serialized, inputConstraints : Expr) : Option[Seq[Expr]] = {
    try {
      /*
      Some(chooseExec(serializedProg, serializedExpr, serializedOutputVars, inputConstraints))
      */
      throw new Exception("not implemented")
    } catch {
      case e: UnsatisfiableConstraintException  => None
      case e: UnknownConstraintException        => None
    }
  }

  def findMinimizingExec(serializedProg : Serialized, serializedExpr : Serialized, serializedOutputVars : Serialized, serializedMinExpr : Serialized, inputConstraints : Expr) : Option[Seq[Expr]] = {
    try {
      Some(chooseMinimizingExec(serializedProg, serializedExpr, serializedOutputVars, serializedMinExpr, inputConstraints))
    } catch {
      case e: UnsatisfiableConstraintException  => None
      case e: UnknownConstraintException        => None
    }
  }

  def findMaximizingExec(serializedProg : Serialized, serializedExpr : Serialized, serializedOutputVars : Serialized, serializedMaxExpr : Serialized, inputConstraints : Expr) : Option[Seq[Expr]] = {
    try {
      Some(chooseMaximizingExec(serializedProg, serializedExpr, serializedOutputVars, serializedMaxExpr, inputConstraints))
    } catch {
      case e: UnsatisfiableConstraintException  => None
      case e: UnknownConstraintException        => None
    }
  }

  def findAllExec(serializedProg : Serialized, serializedExpr : Serialized, serializedOutputVars : Serialized, inputConstraints : Expr) : Iterator[Seq[Expr]] = {
    val program    = deserialize[Program](serializedProg)
    val expr       = deserialize[Expr](serializedExpr)
    val outputVars = deserialize[Seq[Identifier]](serializedOutputVars)

    findAllExec(program, expr, outputVars, inputConstraints)
  }

  private def findAllExec(program : Program, expr : Expr, outputVars : Seq[Identifier], inputConstraints : Expr) : Iterator[Seq[Expr]] = {
    val modelIterator = solutionsIterator(program, expr, inputConstraints, outputVars.toSet)
    val exprIterator  = modelIterator.map(model => outputVars.map(id => model(id)))

    exprIterator
  }

  def findAllMinimizingExec(serializedProg : Serialized, serializedExpr : Serialized, serializedOutputVars : Serialized, serializedMinExpr : Serialized, inputConstraints : Expr) : Iterator[Seq[Expr]] = {
    val program    = deserialize[Program](serializedProg)
    val expr       = deserialize[Expr](serializedExpr)
    val outputVars = deserialize[Seq[Identifier]](serializedOutputVars)
    val minExpr    = deserialize[Expr](serializedMinExpr)

    findAllMinimizingExec(program, expr, outputVars, minExpr, None, inputConstraints)
  }

  private def findAllMinimizingExec(program : Program, expr : Expr, outputVars : Seq[Identifier], minExpr : Expr, minExprBound : Option[Int], inputConstraints : Expr) : Iterator[Seq[Expr]] = {
    try {
      val toCheck = minExprBound match {
        case None => expr
        case Some(b) => And(expr, GreaterThan(minExpr, IntLiteral(b)))
      }
      // purescala.Settings.reporter.info("Now calling findAllMinimizing with " + toCheck)
      val minValue = chooseMinimizingModelAndValue(program, toCheck, outputVars, minExpr, inputConstraints)._2

      val minValConstraint    = And(expr, Equals(minExpr, IntLiteral(minValue)))
      val minValModelIterator = solutionsIterator(program, minValConstraint, inputConstraints, outputVars.toSet)
      val minValExprIterator  = minValModelIterator.map(model => outputVars.map(id => model(id)))

      minValExprIterator ++ findAllMinimizingExec(program, expr, outputVars, minExpr, Some(minValue), inputConstraints)
    } catch {
      case e: UnsatisfiableConstraintException  => Iterator[Seq[Expr]]()
      case e: UnknownConstraintException        => Iterator[Seq[Expr]]()
    }
  }

  private def modelValue(varId: Identifier, model: Map[Identifier, Expr]) : Expr = model.get(varId) match {
    case Some(value) => value
    case None => simplestValue(varId.getType)
  }

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

  /** Returns an iterator of interpretations for each identifier in the specified set */
  private def solutionsIterator(program : Program, predicate : Expr, inputEqualities : Expr, outputVariables : Set[Identifier]) : Iterator[Map[Identifier, Expr]] = {
    val solver = newSolver()
    solver.setProgram(program)
    solver.restartZ3

    new Iterator[Map[Identifier, Expr]] {

      // If nextModel is None, we do not know yet whether there is a next element
      var nextModel: Option[Option[Map[Identifier, Expr]]] = None

      // We add after finding each model the negation of the previous one
      var addedNegations: Expr = BooleanLiteral(true)

      var toCheck: Expr = And(inputEqualities, predicate)

      override def hasNext : Boolean = nextModel match {
        case None => 
          // Check whether there are any more models
          val stopwatch = new Stopwatch("hasNext", false).start
          val (outcome, model) = solver.decideWithModel(toCheck, false)
          stopwatch.stop
          stopwatch.writeToSummary
          val toReturn = (outcome match {
            case Some(false) =>
              // there is a solution, we need to complete model for nonmentioned variables
              val completeModel = outputVariables.foldLeft(model){
                case (modelSoFar, ov) => modelSoFar.get(ov) match {
                  case None =>
                    // model has to be augmented for ov
                    modelSoFar + (ov -> simplestValue(ov.getType))
                  case _ =>
                    modelSoFar
                }
              }
              nextModel = Some(Some(completeModel))
              val newModelEqualities = And(outputVariables.map(ov => Equals(Variable(ov), completeModel(ov))).toList)
              toCheck = negate(newModelEqualities)
              true
            case Some(true) =>
              // there are definitely no more solutions
              nextModel = Some(None)
              false
            case None =>
              // unknown
              nextModel = Some(None)
              false
          })
          toReturn
        case Some(None) =>
          // There are no more models
          false
        case Some(Some(map)) =>
          true
      }

      override def next() : Map[Identifier, Expr] = nextModel match {
        case None => {
          // Let's compute the next model
          val (outcome, model) = solver.decideWithModel(toCheck, false)
          val toReturn = (outcome match {
            case Some(false) =>
              // there is a solution, we need to complete model for nonmentioned variables
              val completeModel = outputVariables.foldLeft(model){
                case (modelSoFar, ov) => modelSoFar.get(ov) match {
                  case None =>
                    // model has to be augmented for ov
                    modelSoFar + (ov -> simplestValue(ov.getType))
                  case _ =>
                    modelSoFar
                }
              }

              val newModelEqualities = And(outputVariables.map(ov => Equals(Variable(ov), completeModel(ov))).toList)
              toCheck = negate(newModelEqualities)
              completeModel
            case Some(true) =>
              // Definitely no more solutions
              throw new Exception("Requesting a new model while there are no more")
            case None =>
              // Unknown
              throw new Exception("Requesting a new model while there are no more")
          })
          toReturn
        }
        case Some(Some(m)) =>
          nextModel = None
          m
        case Some(None) =>
          throw new Exception("Requesting a new model while the last result was unknown")
      }
    }
  }
}
