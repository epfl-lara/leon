package cp

/** A collection of methods that are called on runtime */
object RuntimeMethods {
  import Serialization._
  import Terms._
  import Definitions.UnsatisfiableConstraintException
  import Definitions.UnknownConstraintException
  import LTrees._

  import purescala.Definitions._
  import purescala.Trees._
  import purescala.TypeTrees._
  import purescala.Common._
  import purescala.{DefaultReporter,QuietReporter}
  import purescala.FairZ3Solver

  import purescala.Stopwatch
  
  /* WILL BE PORTED TO Terms.scala
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
          case e => scala.sys.error("Unexpected value for term to maximize : " + e)
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

    Settings.useScalaEvaluator              = recovered.useScalaEvaluator
    Settings.verbose                        = recovered.verbose
  }
  
  def inputVar(inputVarList : List[Variable], varName : String) : Variable = {
    inputVarList.find(_.id.name == varName).getOrElse(scala.sys.error("Could not find input variable '" + varName + "' in list " + inputVarList))
  }

  def variableFromL[T](l: L[T]): Variable = {
    val ids = l.ids
    assert(ids.size == 1)
    Variable(ids.head)
  }

  def isSet(a: Any): Boolean = a.isInstanceOf[Set[_]]
  def isMap(a: Any): Boolean = a.isInstanceOf[Map[_,_]]
  def isFunction(a: Any): Boolean = a.isInstanceOf[Function1[_,_]]

  def toScalaMap(e: Expr, e2s: (Expr) => Any): Map[_,_] = e match {
    case FiniteMap(ss) => (ss.map{
      case SingletonMap(k, v) => (e2s(k), e2s(v))
    }).toMap
    case _ => sys.error("Trying to convert " + e + " to a Scala map")
  }

  def toScalaSet(e: Expr, e2s: (Expr) => Any): Set[_] = e match {
    case FiniteSet(es) => es.map(e => e2s(e)).toSet
    case _ => sys.error("Trying to convert " + e + " to a Scala set")
  }

  def toScalaFunction(e: Expr, e2s: (Expr) => Any): Any = (e, e.getType) match {
    case (AnonymousFunction(es, ev), FunctionType(fts, tt)) => {
      throw new Exception("TODO")
    }
    case _ => sys.error("Trying to convert " + e + " to a Scala set")
  }
}
