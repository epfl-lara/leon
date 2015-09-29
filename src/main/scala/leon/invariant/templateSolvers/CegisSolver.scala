package leon
package invariant.templateSolvers
import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import java.io._
import scala.util.control.Breaks._
import solvers._
import solvers.z3._
import invariant.engine._
import invariant.factories._
import invariant.util._
import invariant.structure._
import invariant.structure.FunctionUtils._
import leon.invariant.util.RealValuedExprEvaluator._

class CegisSolver(ctx: InferenceContext,
  rootFun: FunDef,
  ctrTracker: ConstraintTracker,
  timeout: Int,
  bound: Option[Int] = None) extends TemplateSolver(ctx, rootFun, ctrTracker) {

  override def solve(tempIds: Set[Identifier], funcVCs: Map[FunDef, Expr]): (Option[Model], Option[Set[Call]]) = {

    val initCtr = if (bound.isDefined) {
      //use a predefined bound on the template variables
      Util.createAnd(tempIds.map((id) => {
        val idvar = id.toVariable
        And(Implies(LessThan(idvar, realzero), GreaterEquals(idvar, InfiniteIntegerLiteral(-bound.get))),
          Implies(GreaterEquals(idvar, realzero), LessEquals(idvar, InfiniteIntegerLiteral(bound.get))))
      }).toSeq)

    } else tru

    val funcs = funcVCs.keys
    val formula = Util.createOr(funcs.map(funcVCs.apply _).toSeq)

    //using reals with bounds does not converge and also results in overflow
    val (res, _, model) = (new CegisCore(ctx, timeout, this)).solve(tempIds, formula, initCtr, solveAsInt = true)
    res match {
      case Some(true) => (Some(model), None)
      case Some(false) => (None, None) //no solution exists
      case _ => //timed out
        throw new IllegalStateException("Timeout!!")
    }
  }
}

class CegisCore(ctx: InferenceContext,
  timeout: Int,
  cegisSolver: TemplateSolver) {

  val fls = BooleanLiteral(false)
  val tru = BooleanLiteral(true)
  val zero = InfiniteIntegerLiteral(0)
  val timeoutMillis = timeout.toLong * 1000
  val dumpCandidateInvs = true
  val minimizeSum = false
  val program = ctx.program
  val context = ctx.leonContext
  val reporter = context.reporter

  /**
   * Finds a model for the template variables in the 'formula' so that 'formula' is falsified
   * subject to the constraints on the template variables given by the 'envCtrs'
   *
   * The parameter solveAsInt when set to true will convert the template constraints
   * to integer constraints and solve. This should be enabled when bounds are used to constrain the variables
   */
  def solve(tempIds: Set[Identifier], formula: Expr, initCtr: Expr, solveAsInt: Boolean,
    initModel: Option[Model] = None): (Option[Boolean], Expr, Model) = {

    //start a timer
    val startTime = System.currentTimeMillis()

    //for some sanity checks
    var oldModels = Set[Expr]()
    def addModel(m: Model) = {
      val mexpr = Util.modelToExpr(m)
      if (oldModels.contains(mexpr))
        throw new IllegalStateException("repeating model !!:" + m)
      else oldModels += mexpr
    }

    //add the initial model
    val simplestModel = if (initModel.isDefined) initModel.get else {
      new Model(tempIds.map((id) => (id -> simplestValue(id.getType))).toMap)
    }
    addModel(simplestModel)

    val tempVarSum = if (minimizeSum) {
      //compute the sum of the tempIds
      val rootTempIds = Util.getTemplateVars(cegisSolver.rootFun.getTemplate)
      if (rootTempIds.size >= 1) {
        rootTempIds.tail.foldLeft(rootTempIds.head.asInstanceOf[Expr])((acc, tvar) => Plus(acc, tvar))
      } else zero
    } else zero

    //convert initCtr to a real-constraint
    val initRealCtr = ExpressionTransformer.IntLiteralToReal(initCtr)
    if (Util.hasInts(initRealCtr))
      throw new IllegalStateException("Initial constraints have integer terms: " + initRealCtr)

    def cegisRec(model: Model, prevctr: Expr): (Option[Boolean], Expr, Model) = {

      val elapsedTime = (System.currentTimeMillis() - startTime)
      if (elapsedTime >= timeoutMillis - 100) {
        //if we have timed out return the present set of constrains and the current model we have
        (None, prevctr, model)
      } else {

        //println("elapsedTime: "+elapsedTime / 1000+" timeout: "+timeout)
        Stats.updateCounter(1, "CegisIters")

        if (dumpCandidateInvs) {
          reporter.info("Candidate invariants")
          val candInvs = cegisSolver.getAllInvariants(model)
          candInvs.foreach((entry) => println(entry._1.id + "-->" + entry._2))
        }
        val tempVarMap: Map[Expr, Expr] = model.map((elem) => (elem._1.toVariable, elem._2)).toMap
        val instFormula = simplifyArithmetic(TemplateInstantiator.instantiate(formula, tempVarMap))

        //sanity checks
        val spuriousTempIds = variablesOf(instFormula).intersect(TemplateIdFactory.getTemplateIds)
        if (!spuriousTempIds.isEmpty)
          throw new IllegalStateException("Found a template variable in instFormula: " + spuriousTempIds)
        if (Util.hasReals(instFormula))
          throw new IllegalStateException("Reals in instFormula: " + instFormula)

        //println("solving instantiated vcs...")
        val t1 = System.currentTimeMillis()
        val solver1 = new ExtendedUFSolver(context, program)
        solver1.assertCnstr(instFormula)
        val res = solver1.check
        val t2 = System.currentTimeMillis()
        println("1: " + (if (res.isDefined) "solved" else "timedout") + "... in " + (t2 - t1) / 1000.0 + "s")

        res match {
          case Some(true) => {
            //simplify the tempctrs, evaluate every atom that does not involve a template variable
            //this should get rid of all functions
            val satctrs =
              simplePreTransform((e) => e match {
                //is 'e' free of template variables ?
                case _ if (variablesOf(e).filter(TemplateIdFactory.IsTemplateIdentifier _).isEmpty) => {
                  //evaluate the term
                  val value = solver1.evalExpr(e)
                  if (value.isDefined) value.get
                  else throw new IllegalStateException("Cannot evaluate expression: " + e)
                }
                case _ => e
              })(Not(formula))
            solver1.free()

            //sanity checks
            val spuriousProgIds = variablesOf(satctrs).filterNot(TemplateIdFactory.IsTemplateIdentifier _)
            if (!spuriousProgIds.isEmpty)
              throw new IllegalStateException("Found a progam variable in tempctrs: " + spuriousProgIds)

            val tempctrs = if (!solveAsInt) ExpressionTransformer.IntLiteralToReal(satctrs) else satctrs
            val newctr = And(tempctrs, prevctr)
            //println("Newctr: " +newctr)

            if (ctx.dumpStats) {
              Stats.updateCounterStats(Util.atomNum(newctr), "CegisTemplateCtrs", "CegisIters")
            }

            //println("solving template constraints...")
            val t3 = System.currentTimeMillis()
            val elapsedTime = (t3 - startTime)
            val solver2 = SimpleSolverAPI(new TimeoutSolverFactory(SolverFactory(() => new ExtendedUFSolver(context, program) with TimeoutSolver),
              timeoutMillis - elapsedTime))

            val (res1, newModel) = if (solveAsInt) {
              //convert templates to integers and solve. Finally, re-convert integer models for templates to real models
              val rti = new RealToInt()
              val intctr = rti.mapRealToInt(And(newctr, initRealCtr))
              val intObjective = rti.mapRealToInt(tempVarSum)
              val (res1, intModel) = if (minimizeSum) {
                minimizeIntegers(intctr, intObjective)
              } else {
                solver2.solveSAT(intctr)
              }
              (res1, rti.unmapModel(intModel))
            } else {

              /*if(InvariantUtil.hasInts(tempctrs))
            	throw new IllegalStateException("Template constraints have integer terms: " + tempctrs)*/
              if (minimizeSum) {
                minimizeReals(And(newctr, initRealCtr), tempVarSum)
              } else {
                solver2.solveSAT(And(newctr, initRealCtr))
              }
            }

            val t4 = System.currentTimeMillis()
            println("2: " + (if (res1.isDefined) "solved" else "timed out") + "... in " + (t4 - t3) / 1000.0 + "s")

            if (res1.isDefined) {
              if (res1.get == false) {
                //there exists no solution for templates
                (Some(false), newctr, Model.empty)

              } else {
                //this is for sanity check
                addModel(newModel)
                //generate more constraints
                cegisRec(newModel, newctr)
              }
            } else {
              //we have timed out
              (None, prevctr, model)
            }
          }
          case Some(false) => {
            solver1.free()
            //found a model for disabling the formula
            (Some(true), prevctr, model)
          } case _ => {
            solver1.free()
            throw new IllegalStateException("Cannot solve instFormula: " + instFormula)
          }
        }
      }
    }
    //note: initRealCtr is used inside 'cegisRec'
    cegisRec(simplestModel, tru)
  }

  /**
   * Performs minimization
   */
  val MaxIter = 16 //note we may not be able to represent anything beyond 2^16
  val MaxInt = Int.MaxValue
  val sqrtMaxInt = 45000
  val half = FractionalLiteral(1, 2)
  val two = FractionalLiteral(2, 1)
  val rzero = FractionalLiteral(0, 1)
  val mone = FractionalLiteral(-1, 1)
  val debugMinimization = false

  def minimizeReals(inputCtr: Expr, objective: Expr): (Option[Boolean], Model) = {
    //val t1 = System.currentTimeMillis()
    val sol = SimpleSolverAPI(new TimeoutSolverFactory(SolverFactory(() => new ExtendedUFSolver(context, program) with TimeoutSolver), timeoutMillis))
    val (res, model1) = sol.solveSAT(inputCtr)
    res match {
      case Some(true) => {
        //do a binary search on sequentially on each of these tempvars
        println("minimizing " + objective + " ...")
        val idMap: Map[Expr, Expr] = variablesOf(objective).map(id => (id.toVariable -> model1(id))).toMap
        var upperBound: FractionalLiteral = evaluate(replace(idMap, objective))
        var lowerBound: Option[FractionalLiteral] = None
        var currentModel = model1
        var continue = true
        var iter = 0
        do {
          iter += 1
          //here we perform some sanity checks to prevent overflow
          if (!boundSanityChecks(upperBound, lowerBound)) {
            continue = false
          } else {
            if (lowerBound.isDefined && evaluateRealPredicate(GreaterEquals(lowerBound.get, upperBound))) {
              continue = false
            } else {

              val currval = if (lowerBound.isDefined) {
                val midval = evaluate(Times(half, Plus(upperBound, lowerBound.get)))
                floor(midval)

              } else {
                val rlit @ FractionalLiteral(n, d) = upperBound
                if (isGEZ(rlit)) {
                  if (n == 0) {
                    //make the upper bound negative
                    mone
                  } else {
                    floor(evaluate(Times(half, upperBound)))
                  }
                } else floor(evaluate(Times(two, upperBound)))

              }
              val boundCtr = LessEquals(objective, currval)
              //val t1 = System.currentTimeMillis()
              val solver2 = SimpleSolverAPI(new TimeoutSolverFactory(SolverFactory(() => new ExtendedUFSolver(context, program) with TimeoutSolver), timeoutMillis))
              val (res, newModel) = sol.solveSAT(And(inputCtr, boundCtr))
              //val t2 = System.currentTimeMillis()
              //println((if (res.isDefined) "solved" else "timed out") + "... in " + (t2 - t1) / 1000.0 + "s")
              res match {
                case Some(true) => {
                  //here we have a new upper bound
                  currentModel = newModel
                  val idMap: Map[Expr, Expr] = variablesOf(objective).map(id => (id.toVariable -> newModel(id))).toMap
                  val value = evaluate(replace(idMap, objective))
                  upperBound = value
                  if (this.debugMinimization)
                    reporter.info("Found new upper bound: " + upperBound)
                }
                case _ => {
                  //here we have a new lower bound : currval
                  lowerBound = Some(currval)
                  if (this.debugMinimization)
                    reporter.info("Found new lower bound: " + currval)
                }
              }
            }
          }
        } while (continue && iter < MaxIter)
        //here, we found a best-effort minimum
        reporter.info("Minimization complete...")
        (Some(true), currentModel)
      }
      case _ => (res, model1)
    }
  }

  def boundSanityChecks(ub: FractionalLiteral, lb: Option[FractionalLiteral]): Boolean = {
    val FractionalLiteral(n, d) = ub
    if (n <= (MaxInt / 2)) {
      if (lb.isDefined) {
        val FractionalLiteral(n2, _) = lb.get
        (n2 <= sqrtMaxInt && d <= sqrtMaxInt)
      } else {
        (d <= (MaxInt / 2))
      }
    } else false
  }

  def minimizeIntegers(inputCtr: Expr, objective: Expr): (Option[Boolean], Model) = {
    //val t1 = System.currentTimeMillis()
    val sol = SimpleSolverAPI(new TimeoutSolverFactory(SolverFactory(() => new ExtendedUFSolver(context, program) with TimeoutSolver), timeoutMillis))
    val (res, model1) = sol.solveSAT(inputCtr)
    res match {
      case Some(true) => {
        //do a binary search on sequentially on each of these tempvars
        reporter.info("minimizing " + objective + " ...")
        val idMap: Map[Expr, Expr] = variablesOf(objective).map(id => (id.toVariable -> model1(id))).toMap
        var upperBound = simplifyArithmetic(replace(idMap, objective)).asInstanceOf[InfiniteIntegerLiteral].value
        var lowerBound: Option[BigInt] = None
        var currentModel = model1
        var continue = true
        var iter = 0
        do {
          iter += 1
          if (lowerBound.isDefined && lowerBound.get >= upperBound - 1) {
            continue = false
          } else {

            val currval = if (lowerBound.isDefined) {
              val sum = (upperBound + lowerBound.get)
              floorDiv(sum, 2)
            } else {
              if (upperBound >= 0) {
                if (upperBound == 0) {
                  //make the upper bound negative
                  BigInt(-1)
                } else {
                  floorDiv(upperBound, 2)
                }
              } else 2 * upperBound
            }
            val boundCtr = LessEquals(objective, InfiniteIntegerLiteral(currval))
            //val t1 = System.currentTimeMillis()
            val solver2 = SimpleSolverAPI(new TimeoutSolverFactory(SolverFactory(() => new ExtendedUFSolver(context, program) with TimeoutSolver), timeoutMillis))
            val (res, newModel) = sol.solveSAT(And(inputCtr, boundCtr))
            //val t2 = System.currentTimeMillis()
            //println((if (res.isDefined) "solved" else "timed out") + "... in " + (t2 - t1) / 1000.0 + "s")
            res match {
              case Some(true) => {
                //here we have a new upper bound
                currentModel = newModel
                val idMap: Map[Expr, Expr] = variablesOf(objective).map(id => (id.toVariable -> newModel(id))).toMap
                val value = simplifyArithmetic(replace(idMap, objective)).asInstanceOf[InfiniteIntegerLiteral].value
                upperBound = value
                if (this.debugMinimization)
                  reporter.info("Found new upper bound: " + upperBound)
              }
              case _ => {
                //here we have a new lower bound : currval
                lowerBound = Some(currval)
                if (this.debugMinimization)
                  reporter.info("Found new lower bound: " + currval)
              }
            }
          }
        } while (continue && iter < MaxIter)
        //here, we found a best-effort minimum
        reporter.info("Minimization complete...")
        (Some(true), currentModel)
      }
      case _ => (res, model1)
    }
  }

  def floorDiv(did: BigInt, div: BigInt): BigInt = {
    if (div <= 0) throw new IllegalStateException("Invalid divisor")
    if (did < 0) {
      if (did % div != 0) did / div - 1
      else did / div
    } else {
      did / div
    }
  }

}