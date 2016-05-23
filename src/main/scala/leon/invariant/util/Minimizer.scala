/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.util

import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import solvers._
import solvers.smtlib.SMTLIBZ3Solver
import invariant.engine.InferenceContext
import invariant.factories._
import leon.invariant.util.RealValuedExprEvaluator._
import Stats._

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

  /**
   * TODO: use incremental solving of z3 when it is  supported in nlsat
   * Do a binary search sequentially on the tempvars ordered by the rate of growth of the term they
   * are a coefficient for.
   */
  def minimizeBounds(nestMap: Map[Variable, Int])(inputCtr: Expr, initModel: Model): Model = {
    val orderedTempVars = nestMap.toSeq.sortWith((a, b) => a._2 >= b._2).map(_._1)
    lazy val solver = new SimpleSolverAPI(new TimeoutSolverFactory(
      SolverFactory.getFromName(leonctx,program)("smt-z3-u"),
      ctx.vcTimeout * 1000))

    reporter.info("minimizing...")
    var currentModel = initModel
    orderedTempVars.foldLeft(inputCtr: Expr)((acc, tvar) => {
      var upperBound = if (currentModel.isDefinedAt(tvar.id)) {
        currentModel(tvar.id).asInstanceOf[FractionalLiteral]
      } else {
        initModel(tvar.id).asInstanceOf[FractionalLiteral]
      }
      //note: the lower bound is an integer by construction (and is by default zero)
      var lowerBound: FractionalLiteral =
        if (tvar == orderedTempVars(0) && lowerBoundMap.contains(tvar))
          lowerBoundMap(tvar)
        else realzero
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
            val boundCtr = And(LessEquals(tvar, currval), GreaterEquals(tvar, lowerBound))
            val (res, newModel) =
              if (ctx.abort) (None, Model.empty)
              else {
                time { solver.solveSAT(And(acc, boundCtr)) }{minTime =>
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
      //A last ditch effort to make the upper bound an integer.
      val currval @ FractionalLiteral(n, d) =
        if (currentModel.isDefinedAt(tvar.id))
          currentModel(tvar.id).asInstanceOf[FractionalLiteral]
        else
          initModel(tvar.id).asInstanceOf[FractionalLiteral]
      if (d != 1 && !ctx.abort) {
        val (res, newModel) = solver.solveSAT(And(acc, Equals(tvar, floor(currval))))
        if (res == Some(true))
          updateState(newModel)
      }
      //here, we found a best-effort minimum
      if (lowerBound != realzero) {
        updateLowerBound(tvar, lowerBound)
      }
      And(acc, Equals(tvar, currval))
    })
    new Model(initModel.map {
      case (id, e) =>
        if (currentModel.isDefinedAt(id))
          (id -> currentModel(id))
        else
          (id -> initModel(id))
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
          val nestLevel = functionNesting(e1)
          updateMax(v, nestLevel)
          nestLevel
        }
        case Times(v @ Variable(id), e2) if (TemplateIdFactory.IsTemplateIdentifier(id)) => {
          val nestLevel = functionNesting(e2)
          updateMax(v, nestLevel)
          nestLevel
        }
        case v @ Variable(id) if (TemplateIdFactory.IsTemplateIdentifier(id)) => {
          updateMax(v, 0)
          0
        }
        case FunctionInvocation(_, args) => 1 + args.foldLeft(0)((acc, arg) => acc + functionNesting(arg))
        case t: Terminal                 => 0
        /*case UnaryOperator(arg, _) => functionNesting(arg)
        case BinaryOperator(a1, a2, _) => functionNesting(a1) + functionNesting(a2)*/
        case Operator(args, _)           => args.foldLeft(0)((acc, arg) => acc + functionNesting(arg))
      }
    }
    functionNesting(template)
    nestMap
  }
}
