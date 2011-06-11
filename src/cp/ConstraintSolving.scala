package cp

import Terms._
import Definitions.{UnsatisfiableConstraintException,UnknownConstraintException}

import purescala.{QuietReporter,DefaultReporter}
import purescala.Trees._
import purescala.TypeTrees._
import purescala.Definitions._
import purescala.Common._
import purescala.FairZ3Solver
import purescala.Stopwatch

object ConstraintSolving {
  private val silent = ! Settings.verbose
  private def newReporter() = if (silent) new QuietReporter() else new DefaultReporter()
  private def newSolver(program : Program) = {
    val s = new FairZ3Solver(newReporter())
    s.setProgram(program)
    s.restartZ3
    s
  }

  private val DEBUG = false

  object GlobalContext {
    private var solver: FairZ3Solver = null
    private var lastModel: Map[Identifier,Expr] = null

    private var liveSet: Set[Identifier] = Set.empty
    // private var alreadyAsserted: Set[(Expr, Set[Expr])] = Set.empty[Expr]
    // private var toNegateForNextModel: Seq[(Seq[Identifier], Seq[Expr])] = Seq.empty

    def kill(id: Identifier): Unit = {
      liveSet = liveSet - id
    }

    def isAlive(id: Identifier): Boolean = {
      liveSet.contains(id)
    }

    def addLive(id: Identifier): Unit = {
      liveSet = liveSet + id
    }

    def initializeIfNeeded(p: Program): Unit = {
      if (solver == null)
        solver = newSolver(p)
    }

    def checkAssumptions(expr: Expr) : Boolean = checkAssumptions(expr, liveSet map (Variable(_)))
    private def checkAssumptions(expr: Expr, assumptions: Set[Expr]): Boolean = {
      if (DEBUG) {
        println("Checking assumptions: " + expr)
        println("live set: " + liveSet)
      }
      // println("To check: " + expr)
      // println("Assumpt.: " + assumptions)
      solver.decideWithModel(expr, false, assumptions = Some(assumptions)) match {
        case (Some(false), model) =>
          lastModel = model
          true
        case _ =>
          false
      }
    }

    // def restart(): Unit = {
    //   // println("restart called")
    //   solver.restartZ3
    //   lastModel = None
    //   isInconsistent = false
    //   alreadyAsserted = Set.empty[Expr]
    //   toNegateForNextModel = Seq.empty
    // }

    def assertConstraint(expr: Expr): Boolean = {
      if (DEBUG)
        println("Asserting constraint: " +expr)
      solver.decideWithModel(expr, false) match {
        case (Some(false), model) =>
          lastModel = model
          true
        case _ =>
          println("UNSAT encountered in global context.")
          lastModel = null
          false
      }
    }

    /** Returns true iff the solver did not already return UNSAT and there is
     * still a model */
    // def checkConsistency(): Boolean = {
    //   !isInconsistent && (lastModel match {
    //     case Some(m) => true
    //     case None =>
    //       assertConstraint(BooleanLiteral(true))
    //   })
    // }

    def findValues(ids: Seq[Identifier]): Seq[Expr] = {
      if (lastModel == null)
        sys.error("Attempting to find values for " + ids.mkString(", ") + " while model is null.")
      ids.map(modelValue(_, lastModel))
    }

    // def registerAsForced(ids: Seq[Identifier], values: Seq[Expr]): Unit = {
    //   toNegateForNextModel = (ids, values) +: toNegateForNextModel
    // }

    // def assertModelNegation(): Unit = {
    //   if (!toNegateForNextModel.isEmpty) {
    //     val equalities: Seq[Expr] = toNegateForNextModel.flatMap{
    //       case (ids, values) => ((ids map (i => Variable(i))) zip values) map { case (i, v) => Equals(i, v) }
    //     }
    //     toNegateForNextModel = Seq.empty
    //     assertConstraint(Not(And(equalities)))
    //   }
    // }
  }

  /** Return interpretation of the constant in model if it exists, the simplest
   * value otherwise */
  private def modelValue(varId: Identifier, model: Map[Identifier, Expr]) : Expr = model.get(varId) match {
    case Some(value) => value
    case None => simplestValue(varId.getType)
  }

  private def evaluator(constraint : Term[_,Boolean], ids : Seq[Identifier]) : Option[(Map[Identifier,Expr])=>Boolean] = {
    if (cp.Settings.useScalaEvaluator && constraint.evaluator != null) {
      Some((m : Map[Identifier,Expr]) => constraint.evaluator(ids.map(modelValue(_, m))))
    } else None
  }

  /** Return a solution as a sequence of expressions */
  def solveExprSeq(constraint : Term[_,Boolean]) : Seq[Expr] = {
    val solver = newSolver(programOf(constraint))

    val (freshOutputIDs, expr) = combineConstraint(constraint)

    val (outcome, model) = solver.decideWithModel(expr, false, evaluator(constraint, freshOutputIDs))

    outcome match {
      case Some(false) =>
        freshOutputIDs.map(id => modelValue(id, model))
      case Some(true) =>
        throw new UnsatisfiableConstraintException()
      case None =>
        throw new UnknownConstraintException()
    }
  }

  /** Return a solution that minimizes the given term, as a sequence of expressions */
  def solveMinimizingExprSeq(constraint : Constraint[_], minFunc : IntTerm[_]) : Seq[Expr] = {
    val program = programOf(constraint)
    val (freshOutputIDs, expr) = combineConstraint(constraint)
    val minExprWithIndices = exprOf(minFunc)

    val funcSignature = typesOf(minFunc)
    val deBruijnIndices = funcSignature.zipWithIndex.map{ case (t, idx) => DeBruijnIndex(idx).setType(t) }
    val minExprWithIDs = replace((deBruijnIndices zip (freshOutputIDs map (Variable(_)))).toMap, minExprWithIndices)

    val (model, value) = minimizingModelAndValue(program, expr, freshOutputIDs, minExprWithIDs)
    model
  }

  /** Return an iterator of solutions as sequences of expressions */
  def findAllExprSeq(constraint : Term[_,Boolean]) : Iterator[Seq[Expr]] = {
    val program = programOf(constraint)
    val (freshOutputIDs, expr) = combineConstraint(constraint)

    val modelIterator = solutionsIterator(program, expr, freshOutputIDs, evaluator(constraint, freshOutputIDs))
    val exprIterator  = modelIterator.map(model => freshOutputIDs.map(id => model(id)))

    exprIterator
  }

  /** Enumerate all solutions ordered by the term to minimize, as sequences of expressions */
  def findAllMinimizingExprSeq(constraint : Constraint[_], minFunc : IntTerm[_]) : Iterator[Seq[Expr]] = {
    val program = programOf(constraint)
    val (freshOutputIDs, expr) = combineConstraint(constraint)
    val minExprWithIndices = exprOf(minFunc)

    val funcSignature = typesOf(minFunc)
    val deBruijnIndices = funcSignature.zipWithIndex.map{ case (t, idx) => DeBruijnIndex(idx).setType(t) }
    val minExprWithIDs = replace((deBruijnIndices zip (freshOutputIDs map (Variable(_)))).toMap, minExprWithIndices)

    findAllMinimizingExprSeq(program, expr, freshOutputIDs, minExprWithIDs, None)
  }

  private def findAllMinimizingExprSeq(program : Program, expr : Expr, outputVars : Seq[Identifier], minExpr : Expr, minExprBound : Option[Int]) : Iterator[Seq[Expr]] = {
    try {
      val toCheck = minExprBound match {
        case None => expr
        case Some(b) => And(expr, GreaterThan(minExpr, IntLiteral(b)))
      }
      // purescala.Settings.reporter.info("Now calling findAllMinimizing with " + toCheck)
      val minValue = minimizingModelAndValue(program, toCheck, outputVars, minExpr)._2

      val minValConstraint    = And(expr, Equals(minExpr, IntLiteral(minValue)))
      val minValModelIterator = solutionsIterator(program, minValConstraint, outputVars)
      val minValExprIterator  = minValModelIterator.map(model => outputVars.map(id => model(id)))

      minValExprIterator ++ findAllMinimizingExprSeq(program, expr, outputVars, minExpr, Some(minValue))
    } catch {
      case e: UnsatisfiableConstraintException  => Iterator[Seq[Expr]]()
      case e: UnknownConstraintException        => Iterator[Seq[Expr]]()
    }
  }


  private def minimizingModelAndValue(program : Program, expr : Expr, outputVars : Seq[Identifier], minExpr : Expr) : (Seq[Expr], Int) = {
    def stop(lo : Option[Int], hi : Int) : Boolean = lo match {
      case Some(l) => hi - l <= 2
      case None => false
    }
    
    val solver = newSolver(program)

    /* invariant : lo is always stricly less than any sat. minExpr assignment,
     * and there is always a sat. assignment less than hi */
    def minAux(pivot : Int, lo : Option[Int], hi : Int) : (Map[Identifier, Expr], Int) = {
      // println("Iterating:")
      // println("  lo     : " + (lo match { case Some(l) => l; case None => "-inf"}))
      // println("  pivot  : " + pivot)
      // println("  hi     : " + hi)
      // println
      val toCheck = expr :: LessEquals(minExpr, IntLiteral(pivot)) :: Nil
      solver.restartZ3
      val (outcome, model) = solver.decideWithModel(And(toCheck), false)

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

    solver.restartZ3
    solver.decideWithModel(And(expr :: Equals(minExpr, Variable(minExprID)) :: Nil), false) match {
      case (Some(false), model) =>
        // there is a satisfying assignment
        val minExprVal = modelValue(minExprID, model) match {
          case IntLiteral(i) => i
          case e => scala.sys.error("Unexpected value for term to minimize : " + e)
        }

        val (optimalModel, optimalValue) = minAux(minExprVal - 1, None, minExprVal + 1)
        (outputVars.map(v => modelValue(v, optimalModel)), optimalValue)
      case (Some(true), _) =>
        throw new UnsatisfiableConstraintException()
      case _ =>
        throw new UnknownConstraintException()
    }
  }
  /** Returns an iterator of interpretations for each identifier in the specified set */
  private def solutionsIterator(program : Program, predicate : Expr, outputVariables : Seq[Identifier], evaluator : Option[(Map[Identifier,Expr]) => Boolean] = None) : Iterator[Map[Identifier, Expr]] = {
    val solver = newSolver(program)

    new Iterator[Map[Identifier, Expr]] {

      // If nextModel is None, we do not know yet whether there is a next element
      var nextModel: Option[Option[Map[Identifier, Expr]]] = None

      // We add after finding each model the negation of the previous one
      var addedNegations: Expr = BooleanLiteral(true)

      var toCheck: Expr = predicate
      var toUseAsEvaluator : Option[(Map[Identifier,Expr]) => Boolean] = evaluator

      override def hasNext : Boolean = nextModel match {
        case None => 
          // Check whether there are any more models
          val stopwatch = new Stopwatch("hasNext", false).start
          val (outcome, model) = solver.decideWithModel(toCheck, false, toUseAsEvaluator)
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
              val newModelEqualities = And(outputVariables.map(ov => Equals(Variable(ov), completeModel(ov))))
              toCheck = negate(newModelEqualities)
              // accumulate negations of models in evaluator
              // toUseAsEvaluator = toUseAsEvaluator.map(e => ((m : Map[Identifier,Expr]) => e(m) && !m.forall{ case (k,v) => completeModel.get(k) == Some(v) }))
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

              val newModelEqualities = And(outputVariables.map(ov => Equals(Variable(ov), completeModel(ov))))
              toCheck = negate(newModelEqualities)
              // accumulate negations of models in evaluator
              // toUseAsEvaluator = toUseAsEvaluator.map(e => ((m : Map[Identifier,Expr]) => e(m) && !m.forall(p => completeModel.get(p._1) == Some(p._2))))
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
