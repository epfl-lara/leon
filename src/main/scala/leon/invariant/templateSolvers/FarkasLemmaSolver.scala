package leon
package invariant.templateSolvers

import z3.scala._
import purescala._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import java.io._
import solvers.SimpleSolverAPI
import scala.collection.mutable.{ Map => MutableMap }
import invariant.engine._
import invariant.factories._
import invariant.util.Util._
import invariant.util._
import invariant.structure._
import leon.solvers.TimeoutSolver
import leon.solvers.SolverFactory
import leon.solvers.TimeoutSolverFactory
import leon.solvers.Model
import leon.invariant.util.RealValuedExprEvaluator._

class FarkasLemmaSolver(ctx: InferenceContext) {

  //debug flags
  val verbose = true
  val verifyModel = false
  val dumpNLCtrsAsSMTLIB = false
  val dumpNLCtrs = false
  val debugNLCtrs = false

  // functionality flags
  val solveAsBitvectors = false
  val bvsize = 5
  val useIncrementalSolvingForNLctrs = false //note: NLsat doesn't support incremental solving. It starts from sratch even in incremental solving.

  val leonctx = ctx.leonContext
  val program = ctx.program
  val reporter = ctx.reporter
  val timeout = ctx.timeout
  /**
   * This procedure produces a set of constraints that need to be satisfiable for the
   * conjunction ants and conseqs to be false
   * antsSimple - antecedents without template variables
   * antsTemp - antecedents with template variables
   * Similarly for conseqsSimple and conseqsTemp
   *
   * Let A,A' and C,C' denote the simple and templated portions of the antecedent and the consequent respectively.
   * We need to check \exists a, \forall x, A[x] ^ A'[x,a] ^ C[x] ^ C'[x,a] = false
   *
   */
  def constraintsForUnsat(linearCtrs: Seq[LinearConstraint], temps: Seq[LinearTemplate]): Expr = {

    //for debugging
    /*println("#" * 20)
    println(allAnts + " ^ " + allConseqs)
    println("#" * 20)*/
    this.applyFarkasLemma(linearCtrs ++ temps, Seq(), true)
  }

  /**
   * This procedure produces a set of constraints that need to be satisfiable for the implication to hold
   * antsSimple - antecedents without template variables
   * antsTemp - antecedents with template variables
   * Similarly for conseqsSimple and conseqsTemp
   *
   * Let A,A' and C,C' denote the simple and templated portions of the antecedent and the consequent respectively.
   * We need to check \exists a, \forall x, A[x] ^ A'[x,a] => C[x] ^ C'[x,a]
   *
   */
  def constraintsForImplication(antsSimple: Seq[LinearConstraint], antsTemp: Seq[LinearTemplate],
    conseqsSimple: Seq[LinearConstraint], conseqsTemp: Seq[LinearTemplate],
    uisolver: SimpleSolverAPI): Expr = {

    val allAnts = antsSimple ++ antsTemp
    val allConseqs = conseqsSimple ++ conseqsTemp
    //for debugging
    println("#" * 20)
    println(allAnts + " => " + allConseqs)
    println("#" * 20)

    //Optimization 1: Check if ants are unsat (already handled)
    val pathVC = createAnd(antsSimple.map(_.toExpr).toSeq ++ conseqsSimple.map(_.toExpr).toSeq)
    val notPathVC = And(createAnd(antsSimple.map(_.toExpr).toSeq), Not(createAnd(conseqsSimple.map(_.toExpr).toSeq)))
    val (satVC, _) = uisolver.solveSAT(pathVC)
    val (satNVC, _) = uisolver.solveSAT(notPathVC)

    //Optimization 2: use the unsatisfiability of VC and not VC to simplify the constraint generation
    //(a) if A => C is false and A' is true then the entire formula is unsat
    //(b) if A => C is false and A' is not true then we need to ensure A^A' is unsat (i.e, disable Ant)
    //(c) if A => C is true (i.e, valid) then it suffices to ensure A^A' => C' is valid
    //(d) if A => C is neither true nor false then we cannot do any simplification
    //TODO: Food for thought:
    //(a) can we do any simplification for case (d) with the model
    //(b) could the linearity in the disabled case be exploited
    val (ants, conseqs, disableFlag) = (satVC, satNVC) match {
      case (Some(false), _) if (antsTemp.isEmpty) => (Seq(), Seq(), false)
      case (Some(false), _) => (allAnts, Seq(), true) //here only disable the antecedents
      case (_, Some(false)) => (allAnts, conseqsTemp, false) //here we need to only check the inductiveness of the templates
      case _ => (allAnts, allConseqs, false)
    }
    if (ants.isEmpty) {
      BooleanLiteral(false)
    } else {
      this.applyFarkasLemma(ants, conseqs, disableFlag)
    }
  }

  /**
   * This procedure uses Farka's lemma to generate a set of non-linear constraints for the input implication.
   * Note that these non-linear constraints are in real arithmetic.
   * TODO: Correctness issue: need to handle strict inequalities in consequent
   * Do we really need the consequent ??
   */
  def applyFarkasLemma(ants: Seq[LinearTemplate], conseqs: Seq[LinearTemplate], disableAnts: Boolean): Expr = {

    //compute the set of all constraint variables in ants
    val antCVars = ants.foldLeft(Set[Expr]())((acc, ant) => acc ++ ant.coeffTemplate.keySet)

    //the creates constraints for a single consequent
    def createCtrs(conseq: Option[LinearTemplate]): Expr = {
      //create a set of identifiers one for each ants
      val lambdas = ants.map((ant) => (ant -> Variable(FreshIdentifier("l", RealType, true)))).toMap
      val lambda0 = Variable(FreshIdentifier("l", RealType, true))

      //add a bunch of constraints on lambdas
      var strictCtrLambdas = Seq[Variable]()
      val lambdaCtrs = (ants.collect((ant) => ant.template match {
        case t: LessEquals => GreaterEquals(lambdas(ant), zero)
        case t: LessThan => {
          val l = lambdas(ant)
          strictCtrLambdas :+= l
          GreaterEquals(l, zero)
        }
      }).toSeq :+ GreaterEquals(lambda0, zero))

      //add the constraints on constant terms
      val sumConst = ants.foldLeft(UMinus(lambda0): Expr)((acc, ant) => ant.constTemplate match {
        case Some(d) => Plus(acc, Times(lambdas(ant), d))
        case None => acc
      })

      val cvars = antCVars ++ (if (conseq.isDefined) conseq.get.coeffTemplate.keys else Seq())
      //initialize enabled and disabled parts
      var enabledPart: Expr = if (conseq.isDefined) {
        conseq.get.constTemplate match {
          case Some(d) => Equals(d, sumConst)
          case None => Equals(zero, sumConst)
        }
      } else null
      //the disabled part handles strict inequalities as well using Motzkin's transposition
      var disabledPart: Expr =
        if (strictCtrLambdas.isEmpty) Equals(one, sumConst)
        else Or(Equals(one, sumConst),
          And(Equals(zero, sumConst), createOr(strictCtrLambdas.map(GreaterThan(_, zero)))))

      for (cvar <- cvars) {
        //compute the linear combination of all the coeffs of antCVars
        //println("Processing cvar: "+cvar)
        var sumCoeff: Expr = zero
        for (ant <- ants) {
          //handle coefficients here
          if (ant.coeffTemplate.contains(cvar)) {
            val addend = Times(lambdas(ant), ant.coeffTemplate.get(cvar).get)
            if (sumCoeff == zero)
              sumCoeff = addend
            else
              sumCoeff = Plus(sumCoeff, addend)
          }
        }
        //println("sum coeff: "+sumCoeff)
        //make the sum equal to the coeff. of cvar in conseq
        if (conseq.isDefined) {
          enabledPart = And(enabledPart,
            (if (conseq.get.coeffTemplate.contains(cvar))
              Equals(conseq.get.coeffTemplate.get(cvar).get, sumCoeff)
            else Equals(zero, sumCoeff)))
        }

        disabledPart = And(disabledPart, Equals(zero, sumCoeff))
      } //end of cvars loop

      //the final constraint is a conjunction of lambda constraints and disjunction of enabled and disabled parts
      if (disableAnts) And(createAnd(lambdaCtrs), disabledPart)
      else {
        //And(And(lambdaCtrs), enabledPart)
        And(createAnd(lambdaCtrs), Or(enabledPart, disabledPart))
      }
    }

    val ctrs = if (disableAnts) {
      //here conseqs are empty
      createCtrs(None)
    } else {
      val Seq(head, tail @ _*) = conseqs
      val nonLinearCtrs = tail.foldLeft(createCtrs(Some(head)))((acc, conseq) => And(acc, createCtrs(Some(conseq))))
      nonLinearCtrs
    }
    ExpressionTransformer.IntLiteralToReal(ctrs)
  }

  def solveFarkasConstraints(nlctrs: Expr): (Option[Boolean], Model) = {

    // factor out common nonlinear terms and create an equiv-satisfiable constraint
    def reduceCommonNLTerms(ctrs: Expr) = {
      var nlUsage = new CounterMap[Expr]()
      postTraversal{
        case t: Times => nlUsage.inc(t)
        case e => ;
      }(ctrs)
      val repMap = nlUsage.collect{
        case (k, v) if v > 1 =>
          (k -> FreshIdentifier("t", RealType, true).toVariable)
      }.toMap
      createAnd(replace(repMap, ctrs) +: repMap.map {
        case (k, v) => Equals(v, k)
      }.toSeq)
    }

    // try eliminate nonlinearity to whatever extent possible
    var elimMap = Map[Identifier, (Identifier, Identifier)]() // maps the fresh identifiers to the product of the identifiers they represent.
    def reduceNonlinearity(farkasctrs: Expr): Expr = {
      var varCounts = new CounterMap[Identifier]()
      // collect # of uses of each variable
      postTraversal {
        case Variable(id) => varCounts.inc(id)
        case _ => ;
      }(farkasctrs)
      var adnlCtrs = Seq[Expr]()
      val simpCtrs = simplePostTransform {
        case Times(vlb @ Variable(lb), va @ Variable(a)) if (varCounts(lb) == 1 || varCounts(a) == 1) => // is lb or a used only once ?
          // stats
          Stats.updateCumStats(1, "NonlinearMultEliminated")
          val freshid = FreshIdentifier(lb.name + a.name, RealType, true)
          val freshvar = freshid.toVariable
          elimMap += (freshid -> (lb, a))
          if (varCounts(lb) == 1)
            // va = 0 ==> freshvar = 0
            adnlCtrs :+= Implies(Equals(va, realzero), Equals(freshvar, realzero))
          else // here varCounts(a) == 1
            adnlCtrs :+= Implies(Equals(vlb, realzero), Equals(freshvar, realzero))
          freshvar
        case e =>
          e
      }(farkasctrs)
      createAnd(simpCtrs +: adnlCtrs)
    }
    val simpctrs = (reduceCommonNLTerms _ andThen
    					reduceNonlinearity)(nlctrs)

    //for debugging nonlinear constraints
    if (this.debugNLCtrs && Util.hasInts(simpctrs)) {
      throw new IllegalStateException("Nonlinear constraints have integers: " + simpctrs)
    }
    if (verbose && LinearConstraintUtil.isLinear(simpctrs)) {
      reporter.info("Constraints reduced to linear !")
    }
    if (this.dumpNLCtrs) {
      reporter.info("InputCtrs: " + nlctrs)
      reporter.info("SimpCtrs: " + simpctrs)
      if (this.dumpNLCtrsAsSMTLIB) {
        val filename = ctx.program.modules.last.id + "-nlctr" + FileCountGUID.getID + ".smt2"
        if (Util.atomNum(simpctrs) >= 5) {
          if (solveAsBitvectors)
            Util.toZ3SMTLIB(simpctrs, filename, "QF_BV", leonctx, program, useBitvectors = true, bitvecSize = bvsize)
          else
            Util.toZ3SMTLIB(simpctrs, filename, "QF_NRA", leonctx, program)
          reporter.info("NLctrs dumped to: " + filename)
        }
      }
    }

    // solve the resulting constraints using solver
    val innerSolver = if (solveAsBitvectors) {
      throw new IllegalStateException("Not supported now. Will be in the future!")
      //new ExtendedUFSolver(leonctx, program, useBitvectors = true, bitvecSize = bvsize) with TimeoutSolver
    } else {
      new ExtendedUFSolver(leonctx, program) with TimeoutSolver
    }
    val solver = SimpleSolverAPI(new TimeoutSolverFactory(SolverFactory(() => innerSolver), timeout * 1000))
    if (verbose) reporter.info("solving...")
    val t1 = System.currentTimeMillis()
    val (res, model) = solver.solveSAT(simpctrs)
    val t2 = System.currentTimeMillis()
    if (verbose) reporter.info((if (res.isDefined) "solved" else "timed out") + "... in " + (t2 - t1) / 1000.0 + "s")
    Stats.updateCounterTime((t2 - t1), "NL-solving-time", "disjuncts")

    res match {
      case Some(true) =>
        // construct assignments for the variables that were removed during nonlinearity reduction
        def divide(dividend: Expr, divisor: Expr) = {
          divisor match {
            case `realzero` =>
              assert(dividend == realzero)
              // here result can be anything. So make it zero
              realzero
            case _ =>
              val res = evaluate(Division(dividend, divisor))
              res
          }
        }
        val newassignments = elimMap.flatMap {
          case (k, (v1, v2)) =>
            val kval = evaluate(model(k))
            if (model.isDefinedAt(v1) && model.isDefinedAt(v2))
              throw new IllegalStateException(
                s"Variables $v1 and $v2 in an eliminated nonlinearity have models")
            else if (model.isDefinedAt(v1)) {
              val v2val = divide(kval, evaluate(model(v1)))
              Seq((v2 -> v2val))
            } else if (model.isDefinedAt(v2))
              Seq((v1 -> divide(kval, evaluate(model(v2)))))
            else
              // here v1 * v2 = k. Therefore make v1 = k and v2 = 1
              Seq((v1 -> kval), (v2 -> FractionalLiteral(1, 1)))
        }
        val fullmodel = model ++ newassignments
        if (this.verifyModel) {
          //println("Fullmodel: "+fullmodel)
          assert(evaluateRealFormula(replace(
              fullmodel.map { case (k, v) => (k.toVariable, v) }.toMap,
              nlctrs)))
        }
        (res, fullmodel)
      case _ =>
        (res, model)
    }
  }
}