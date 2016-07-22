/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.templateSolvers

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import solvers._
import invariant.engine.InferenceContext
import invariant.factories._
import leon.invariant.util._
import RealValuedExprEvaluator._
import Stats._
import scala.collection.mutable.{ Map => MutableMap }

class Minimizer(ctx: InferenceContext, program: Program) {

  val verbose = false
  val debugMinimization = false
  /**
   * Here we are assuming that that initModel is a model for ctrs
   * TODO: make sure that the template for rootFun is the time template
   */
  val MaxIter = 16 //note we may not be able to represent anything beyond 2^16
  val half = FractionalLiteral(1, 2)
  val two = FractionalLiteral(2, 1)
  val rzero = FractionalLiteral(0, 1)
  val mone = FractionalLiteral(-1, 1)
  val lowerLimit = FractionalLiteral(BigInt(ctx.tightBounds.getOrElse(0): Long), 1)

  private val leonctx = ctx.leonContext
  val reporter = leonctx.reporter

  //for statistics and output
  //store the lowerbounds for each template variables in the template of the rootFun provided it is a time template
  var lowerBoundMap = Map[Variable, FractionalLiteral]()
  def updateLowerBound(tvar: Variable, rval: FractionalLiteral) = {
    //record the lower bound if it exist
    if (lowerBoundMap.contains(tvar)) {
      lowerBoundMap -= tvar
    }
    lowerBoundMap += (tvar -> rval)
  }

  def tightenTimeBounds(timeTemplate: Expr)(inputCtr: Expr, initModel: Model) = {
    //the order in which the template variables are minimized is based on the level of nesting of the  terms
    minimizeBounds(computeCompositionLevel(timeTemplate))(inputCtr, initModel)
  }

  val farkasSolver = new FarkasLemmaSolver(ctx, program)
  /**
   * TODO: use incremental solving of z3 when it is  supported in nlsat
   * Do a binary search sequentially on the tempvars ordered by the rate of growth of the term they
   * are a coefficient for.
   */
  def minimizeBounds(nestMap: Map[Variable, Int])(inputCtr: Expr, initModel: Model): Model = {
    val orderedTempVars = nestMap.toSeq.sortWith((a, b) => a._2 >= b._2).map(_._1)
//    lazy val solver = new SimpleSolverAPI(new TimeoutSolverFactory(
//      SolverFactory.getFromName(leonctx, program)("orb-smt-z3-u"),
//      ctx.vcTimeout * 1000))
    reporter.info("minimizing...")
    var result = Map[Identifier, FractionalLiteral]()
    var currentModel = initModel
    // lookup currentModel, otherwise lookup initModel
    val currentVal = (x: Identifier) => currentModel.getOrElse(x, initModel(x)).asInstanceOf[FractionalLiteral]
    orderedTempVars.foldLeft(inputCtr: Expr)((acc, tvar) => {
      var upperBound = currentVal(tvar.id)
      //note: the lower bound is an integer by construction (and is by default zero)
      var lowerBound: FractionalLiteral =
        if (tvar == orderedTempVars(0) && lowerBoundMap.contains(tvar))
          lowerBoundMap(tvar)
        else lowerLimit
      def updateState(nmodel: Model) = {
        upperBound = nmodel(tvar.id).asInstanceOf[FractionalLiteral]
        currentModel = nmodel
        if (this.debugMinimization)
          reporter.info("Found new upper bound: " + upperBound)
      }
      if (this.debugMinimization)
        reporter.info(s"Minimizing variable: $tvar Initial Bounds: [$upperBound,$lowerBound]")
      var continue = true
      var iter = 0
      do {
        iter += 1
        if (continue) {
          val currval = floor(evaluate(Times(half, Plus(upperBound, lowerBound)))) //make sure that curr val is an integer
          if (evaluateRealPredicate(GreaterEquals(lowerBound, currval))) //check if the lowerbound, if it exists, is < currval
            continue = false
          else {
            // TODO: we can convert this to disjunction if the range is small.
            val boundCtr = And(LessEquals(tvar, currval), GreaterEquals(tvar, lowerBound))
            val (res, newModel) =
              if (ctx.abort) (None, Model.empty)
              else {
                time {
                  farkasSolver.solveFarkasConstraints(And(acc, boundCtr))
                  //solver.solveSAT(And(acc, boundCtr))
                } { minTime =>
                  updateCumTime(minTime, "BinarySearchTime")
                }
              }
            res match {
              case Some(true) =>
                updateState(newModel)
              case _ => //here we have a new lower bound: currval
                lowerBound = currval
                if (this.debugMinimization)
                  reporter.info("Found new lower bound: " + currval)
            }
          }
        }
      } while (!ctx.abort && continue && iter < MaxIter)
      //update lowerbound
      if (lowerBound != lowerLimit) {
        updateLowerBound(tvar, lowerBound)
      }
      //A last ditch effort to make the upper bound an integer.
      val currval @ FractionalLiteral(n, d) = currentVal(tvar.id)
      val intval = if (d != 1 && !ctx.abort) {
        val flcurrval = floor(currval)
        val (res, newModel) =
          farkasSolver.solveFarkasConstraints(And(acc, Equals(tvar, flcurrval)))
        //solver.solveSAT(And(acc, Equals(tvar, floor(currval))))
        if (res == Some(true)) {
          updateState(newModel)
          flcurrval
        } else currval
      } else currval
      // update currentResult
      result += (tvar.id -> intval)
      //And(acc, Equals(tvar, currval))
      replace(Map(tvar -> intval), acc)
    })
    //println("New result: "+results)    
    new Model(initModel.map {
      case (id, _) if result.isDefinedAt(id) => (id -> result(id))
      case (id, _)                           => (id -> currentVal(id))
    }.toMap)
  }

  def checkBoundingInteger(tvar: Variable, rl: FractionalLiteral, nlctr: Expr, solver: SimpleSolverAPI): Option[Model] = {
    val nl @ FractionalLiteral(n, d) = normalizeFraction(rl)
    if (d != 1) {
      val flval = floor(nl)
      val (res, newModel) = solver.solveSAT(And(nlctr, Equals(tvar, flval)))
      res match {
        case Some(true) => Some(newModel)
        case _          => None
      }
    } else None
  }

  /**
   * The following code is little tricky
   */
  def computeCompositionLevel(template: Expr): Map[Variable, Int] = {
    var nestMap = Map[Variable, Int]()

    def updateMax(v: Variable, level: Int) = {
      if (verbose) reporter.info("Nesting level: " + v + "-->" + level)
      if (nestMap.contains(v)) {
        if (nestMap(v) < level) {
          nestMap -= v
          nestMap += (v -> level)
        }
      } else
        nestMap += (v -> level)
    }

    def functionNesting(e: Expr): Int = {
      e match {
        case Times(e1, v @ Variable(id)) if (TemplateIdFactory.IsTemplateIdentifier(id)) => {
          val nestLevel = functionNesting(e1) + 1
          updateMax(v, nestLevel)
          nestLevel
        }
        case Times(v @ Variable(id), e2) if (TemplateIdFactory.IsTemplateIdentifier(id)) => {
          val nestLevel = functionNesting(e2) + 1
          updateMax(v, nestLevel)
          nestLevel
        }
        case v @ Variable(id) if (TemplateIdFactory.IsTemplateIdentifier(id)) => {
          updateMax(v, 0)
          0
        }
        case FunctionInvocation(_, args) => 1 + args.foldLeft(0)((acc, arg) => acc + functionNesting(arg))
        case IfExpr(c, th, el)           => 1 + functionNesting(c) + functionNesting(th) + functionNesting(el)
        case t: Terminal                 => 0
        case Operator(args, _)           => args.foldLeft(0)((acc, arg) => acc + functionNesting(arg))
      }
    }
    functionNesting(template)
    nestMap
  }
}
