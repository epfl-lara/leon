/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers
package unrolling

import purescala.Common._
import purescala.Definitions._
import purescala.Quantification._
import purescala.Constructors._
import purescala.Extractors._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import purescala.TypeOps.bestRealType
import utils._

import theories._
import evaluators._
import Template._

trait UnrollingProcedure extends LeonComponent {
  val name = "Unroll-P"
  val description = "Leon Unrolling Procedure"

  val optUnrollFactor  = LeonLongOptionDef("unrollfactor",  "Number of unfoldings to perform in each unfold step", default = 1, "<PosInt>")
  val optFeelingLucky  = LeonFlagOptionDef("feelinglucky",  "Use evaluator to find counter-examples early", false)
  val optCheckModels   = LeonFlagOptionDef("checkmodels",   "Double-check counter-examples with evaluator", false)
  val optUnrollCores   = LeonFlagOptionDef("unrollcores",   "Use unsat-cores to drive unfolding while remaining fair", false)
  val optUseCodeGen    = LeonFlagOptionDef("codegen",       "Use compiled evaluator instead of interpreter", false)
  val optAssumePre     = LeonFlagOptionDef("assumepre",     "Assume precondition holds (pre && f(x) = body) when unfolding", false)
  val optPartialModels = LeonFlagOptionDef("partialmodels", "Extract domains for quantifiers and bounded first-class functions", false)
  val optSilentErrors  = LeonFlagOptionDef("silenterrors",  "Fail silently into UNKNOWN when encountering an error", false)

  override val definedOptions: Set[LeonOptionDef[Any]] =
    Set(optCheckModels, optFeelingLucky, optUseCodeGen, optUnrollCores, optAssumePre, optUnrollFactor, optPartialModels)
}

object UnrollingProcedure extends UnrollingProcedure

trait AbstractUnrollingSolver[T]
  extends UnrollingProcedure
     with Solver
     with EvaluatingSolver {

  val unfoldFactor     = context.findOptionOrDefault(optUnrollFactor)
  val feelingLucky     = context.findOptionOrDefault(optFeelingLucky)
  val checkModels      = context.findOptionOrDefault(optCheckModels)
  val useCodeGen       = context.findOptionOrDefault(optUseCodeGen)
  val unrollUnsatCores = context.findOptionOrDefault(optUnrollCores)
  val assumePreHolds   = context.findOptionOrDefault(optAssumePre)
  val partialModels    = context.findOptionOrDefault(optPartialModels)
  val silentErrors     = context.findOptionOrDefault(optSilentErrors)

  protected var foundDefinitiveAnswer = false
  protected var definitiveAnswer : Option[Boolean] = None
  protected var definitiveModel  : Model = Model.empty
  protected var definitiveCore   : Set[Expr] = Set.empty

  def check: Option[Boolean] = genericCheck(Set.empty)

  def getModel: Model = if (foundDefinitiveAnswer && definitiveAnswer.getOrElse(false)) {
    definitiveModel
  } else {
    Model.empty
  }

  def getUnsatCore: Set[Expr] = if (foundDefinitiveAnswer && !definitiveAnswer.getOrElse(true)) {
    definitiveCore
  } else {
    Set.empty
  }

  private val constraints = new IncrementalSeq[Expr]()
  private val freeVars    = new IncrementalMap[Identifier, T]()

  protected var interrupted : Boolean = false

  lazy val templateGenerator = new TemplateGenerator(theoryEncoder, templateEncoder, assumePreHolds)
  lazy val unrollingBank = new UnrollingBank(context, templateGenerator)

  def push(): Unit = {
    unrollingBank.push()
    constraints.push()
    freeVars.push()
  }

  def pop(): Unit = {
    unrollingBank.pop()
    constraints.pop()
    freeVars.pop()
  }

  override def reset() = {
    foundDefinitiveAnswer = false
    interrupted = false

    unrollingBank.reset()
    constraints.reset()
    freeVars.reset()
  }

  override def interrupt(): Unit = {
    interrupted = true
  }

  override def recoverInterrupt(): Unit = {
    interrupted = false
  }

  protected def declareVariable(id: Identifier): T

  def assertCnstr(expression: Expr): Unit = {
    constraints += expression
    val bindings = variablesOf(expression).map(id => id -> freeVars.cached(id) {
      declareVariable(theoryEncoder.encode(id))
    }).toMap

    val newClauses = unrollingBank.getClauses(expression, bindings)
    for (cl <- newClauses) {
      solverAssert(cl)
    }
  }

  def foundAnswer(res: Option[Boolean], model: Model = Model.empty, core: Set[Expr] = Set.empty) = {
    foundDefinitiveAnswer = true
    definitiveAnswer = res
    definitiveModel = model
    definitiveCore = core
  }

  implicit val printable: T => Printable

  val theoryEncoder: TheoryEncoder
  val templateEncoder: TemplateEncoder[T]

  def solverAssert(cnstr: T): Unit

  /** We define solverCheckAssumptions in CPS in order for solvers that don't
   *  support this feature to be able to use the provided [[solverCheck]] CPS
   *  construction.
   */
  def solverCheckAssumptions[R](assumptions: Seq[T])(block: Option[Boolean] => R): R =
    solverCheck(assumptions)(block)

  def checkAssumptions(assumptions: Set[Expr]): Option[Boolean] =
    genericCheck(assumptions)

  /** Provides CPS solver.check call. CPS is necessary in order for calls that
   *  depend on solver.getModel to be able to access the model BEFORE the call
   *  to solver.pop() is issued.
   *
   *  The underlying solver therefore performs the following sequence of
   *  solver calls:
   *  {{{
   *    solver.push()
   *    for (cls <- clauses) solver.assertCnstr(cls)
   *    val res = solver.check
   *    block(res)
   *    solver.pop()
   *  }}}
   *
   *  This ordering guarantees that [[block]] can safely call solver.getModel.
   *
   *  This sequence of calls can also be used to mimic solver.checkAssumptions()
   *  for solvers that don't support the construct natively.
   */
  def solverCheck[R](clauses: Seq[T])(block: Option[Boolean] => R): R

  def solverUnsatCore: Option[Seq[T]]

  trait ModelWrapper {
    def modelEval(elem: T, tpe: TypeTree): Option[Expr]

    def eval(elem: T, tpe: TypeTree): Option[Expr] = modelEval(elem, theoryEncoder.encode(tpe)).flatMap {
      expr => try {
        Some(theoryEncoder.decode(expr)(Map.empty))
      } catch {
        case u: Unsupported => None
      }
    }

    def get(id: Identifier): Option[Expr] = eval(freeVars(id), theoryEncoder.encode(id.getType)).filter {
      case Variable(_) => false
      case _ => true
    }

    private[AbstractUnrollingSolver] def extract(b: T, m: Matcher[T]): Option[Seq[Expr]] = {
      val QuantificationTypeMatcher(fromTypes, _) = m.tpe
      val optEnabler = eval(b, BooleanType)
      optEnabler.filter(_ == BooleanLiteral(true)).flatMap { _ =>
        val optArgs = (m.args zip fromTypes).map { case (arg, tpe) => eval(arg.encoded, tpe) }
        if (optArgs.forall(_.isDefined)) {
          Some(optArgs.map(_.get))
        } else {
          None
        }
      }
    }
  }

  def solverGetModel: ModelWrapper

  private def emit(silenceErrors: Boolean)(msg: String) =
    if (silenceErrors) reporter.debug(msg) else reporter.warning(msg)

  private def extractModel(wrapper: ModelWrapper): Model =
    new Model(freeVars.toMap.map(p => p._1 -> wrapper.get(p._1).getOrElse(simplestValue(p._1.getType))))

  private def validateModel(model: Model, assumptions: Seq[Expr], silenceErrors: Boolean): Boolean = {
    val expr = andJoin(assumptions ++ constraints)

    val newExpr = model.toSeq.foldLeft(expr){
      case (e, (k, v)) => let(k, v, e)
    }

    evaluator.eval(newExpr) match {
      case EvaluationResults.Successful(BooleanLiteral(true)) =>
        reporter.debug("- Model validated.")
        true

      case EvaluationResults.Successful(_) =>
        reporter.debug("- Invalid model.")
        false

      case EvaluationResults.RuntimeError(msg) =>
        emit(silenceErrors)("- Model leads to runtime error: " + msg)
        false

      case EvaluationResults.EvaluatorError(msg) =>
        emit(silenceErrors)("- Model leads to evaluation error: " + msg)
        false
    }
  }

  private def getPartialModel: PartialModel = {
    val wrapped = solverGetModel
    val view = templateGenerator.manager.getModel(freeVars.toMap, evaluator, wrapped.get, wrapped.eval)
    view.getPartialModel
  }

  private def getTotalModel: Model = {
    val wrapped = solverGetModel
    val view = templateGenerator.manager.getModel(freeVars.toMap, evaluator, wrapped.get, wrapped.eval)
    view.getTotalModel
  }

  def genericCheck(assumptions: Set[Expr]): Option[Boolean] = {
    foundDefinitiveAnswer = false

    // TODO: theory encoder for assumptions!?
    val encoder = templateGenerator.encoder.encodeExpr(freeVars.toMap) _
    val assumptionsSeq       : Seq[Expr]    = assumptions.toSeq
    val encodedAssumptions   : Seq[T]       = assumptionsSeq.map(encoder)
    val encodedToAssumptions : Map[T, Expr] = (encodedAssumptions zip assumptionsSeq).toMap

    def encodedCoreToCore(core: Seq[T]): Set[Expr] = {
      core.flatMap(ast => encodedToAssumptions.get(ast) match {
        case Some(n @ Not(Variable(_))) => Some(n)
        case Some(v @ Variable(_)) => Some(v)
        case _ => None
      }).toSet
    }

    while (!foundDefinitiveAnswer && !interrupted) {
      reporter.debug(" - Running search...")
      var quantify = false

      def check[R](clauses: Seq[T])(block: Option[Boolean] => R) =
        if (partialModels || templateGenerator.manager.quantifications.isEmpty)
          solverCheckAssumptions(clauses)(block)
        else solverCheck(clauses)(block)

      val timer = context.timers.solvers.check.start()
      check(encodedAssumptions.toSeq ++ unrollingBank.satisfactionAssumptions) { res =>
        timer.stop()

        reporter.debug(" - Finished search with blocked literals")

        res match {
          case None =>
            foundAnswer(None)

          case Some(true) => // SAT
            val (stop, model) = if (interrupted) {
              (true, Model.empty)
            } else if (partialModels) {
              (true, getPartialModel)
            } else {
              val clauses = unrollingBank.getFiniteRangeClauses
              if (clauses.isEmpty) {
                (true, extractModel(solverGetModel))
              } else {
                reporter.debug(" - Verifying model transitivity")

                val timer = context.timers.solvers.check.start()
                solverCheck(clauses) { res =>
                  timer.stop()

                  reporter.debug(" - Finished transitivity check")

                  res match {
                    case Some(true) =>
                      (true, getTotalModel)

                    case Some(false) =>
                      reporter.debug(" - Transitivity not guaranteed for model")
                      (false, Model.empty)

                    case None =>
                      reporter.warning(" - Unknown for transitivity!?")
                      (false, Model.empty)
                  }
                }
              }
            }

            if (!interrupted) {
              if (!stop) {
                if (!unrollingBank.canInstantiate) {
                  reporter.error("Something went wrong. The model is not transitive yet we can't instantiate!?")
                  reporter.error(model.asString(context))
                  foundAnswer(None, model)
                } else {
                  quantify = true
                }
              } else {
                val valid = !checkModels || validateModel(model, assumptionsSeq, silenceErrors = silentErrors)

                if (valid) {
                  foundAnswer(Some(true), model)
                } else if (silentErrors) {
                  foundAnswer(None, model)
                } else {
                  reporter.error(
                    "Something went wrong. The model should have been valid, yet we got this: " +
                    model.asString(context) +
                    " for formula " + andJoin(assumptionsSeq ++ constraints).asString)
                  foundAnswer(None, model)
                }
              }
            }

            if (interrupted) {
              foundAnswer(None)
            }

          case Some(false) if !unrollingBank.canUnroll =>
            solverUnsatCore match {
              case Some(core) =>
                val exprCore = encodedCoreToCore(core)
                foundAnswer(Some(false), core = exprCore)
              case None =>
                foundAnswer(Some(false))
            }

          case Some(false) =>
            if (unrollUnsatCores) {
              solverUnsatCore match {
                case Some(core) =>
                  unrollingBank.decreaseAllGenerations()

                  for (c <- core) templateGenerator.encoder.extractNot(c) match {
                    case Some(b) => unrollingBank.promoteBlocker(b)
                    case None => reporter.fatalError("Unexpected blocker polarity for unsat core unrolling: " + c)
                  }
                case None =>
                  reporter.fatalError("Can't unroll unsat core for incompatible solver " + name)
              }
            }
        }
      }

      if (!quantify && !foundDefinitiveAnswer && !interrupted) {
        if (feelingLucky) {
          reporter.debug(" - Running search without blocked literals (w/ lucky test)")
        } else {
          reporter.debug(" - Running search without blocked literals (w/o lucky test)")
        }

        val timer = context.timers.solvers.check.start()
        solverCheckAssumptions(encodedAssumptions.toSeq ++ unrollingBank.refutationAssumptions) { res2 =>
          timer.stop()

          reporter.debug(" - Finished search without blocked literals")

          res2 match {
            case Some(false) =>
              solverUnsatCore match {
                case Some(core) =>
                  val exprCore = encodedCoreToCore(core)
                  foundAnswer(Some(false), core = exprCore)
                case None =>
                  foundAnswer(Some(false))
              }

            case Some(true) =>
              if (!interrupted) {
                val model = solverGetModel

                if (this.feelingLucky) {
                  // we might have been lucky :D
                  val extracted = extractModel(model)
                  val valid = validateModel(extracted, assumptionsSeq, silenceErrors = true)
                  if (valid) foundAnswer(Some(true), extracted)
                }

                if (!foundDefinitiveAnswer) {
                  val promote = templateGenerator.manager.getBlockersToPromote(model.eval)
                  if (promote.nonEmpty) {
                    unrollingBank.decreaseAllGenerations()

                    for (b <- promote) unrollingBank.promoteBlocker(b, force = true)
                  }
                }
              }

            case None =>
              foundAnswer(None)
          }
        }
      }

      if (!foundDefinitiveAnswer && !interrupted) {
        reporter.debug("- We need to keep going")

        reporter.debug(" - more instantiations")
        val newClauses = unrollingBank.instantiateQuantifiers(force = quantify)

        for (cls <- newClauses) {
          solverAssert(cls)
        }

        reporter.debug(" - finished instantiating")

        // unfolling `unfoldFactor` times
        for (i <- 1 to unfoldFactor.toInt) {
          val toRelease = unrollingBank.getBlockersToUnlock

          reporter.debug(" - more unrollings")

          val timer = context.timers.solvers.unroll.start()
          val newClauses = unrollingBank.unrollBehind(toRelease)
          timer.stop()

          for (ncl <- newClauses) {
            solverAssert(ncl)
          }
        }

        reporter.debug(" - finished unrolling")
      }
    }

    if (interrupted) {
      None
    } else {
      definitiveAnswer
    }
  }
}

class UnrollingSolver(
  val sctx: SolverContext,
  val program: Program,
  underlying: Solver,
  theories: TheoryEncoder = new NoEncoder
) extends AbstractUnrollingSolver[Expr] {

  override val name = "U:"+underlying.name

  def free() {
    underlying.free()
  }

  val printable = (e: Expr) => e

  val templateEncoder = new TemplateEncoder[Expr] {
    def encodeId(id: Identifier): Expr= Variable(id.freshen)
    def encodeExpr(bindings: Map[Identifier, Expr])(e: Expr): Expr = {
      replaceFromIDs(bindings, e)
    }

    def substitute(substMap: Map[Expr, Expr]): Expr => Expr = {
      (e: Expr) => replace(substMap, e)
    }

    def mkNot(e: Expr) = not(e)
    def mkOr(es: Expr*) = orJoin(es)
    def mkAnd(es: Expr*) = andJoin(es)
    def mkEquals(l: Expr, r: Expr) = Equals(l, r)
    def mkImplies(l: Expr, r: Expr) = implies(l, r)

    def extractNot(e: Expr): Option[Expr] = e match {
      case Not(b) => Some(b)
      case _ => None
    }
  }

  val theoryEncoder = theories

  val solver = underlying

  def declareVariable(id: Identifier): Variable = id.toVariable

  def solverAssert(cnstr: Expr): Unit = {
    solver.assertCnstr(cnstr)
  }

  def solverCheck[R](clauses: Seq[Expr])(block: Option[Boolean] => R): R = {
    solver.push()
    for (cls <- clauses) solver.assertCnstr(cls)
    val res = solver.check
    val r = block(res)
    solver.pop()
    r
  }

  def solverUnsatCore = None

  def solverGetModel: ModelWrapper = new ModelWrapper {
    val model = solver.getModel
    def modelEval(elem: Expr, tpe: TypeTree): Option[Expr] = evaluator.eval(elem, model).result
    override def toString = model.toMap.mkString("\n")
  }

  override def dbg(msg: => Any) = underlying.dbg(msg)

  override def push(): Unit = {
    super.push()
    solver.push()
  }

  override def pop(): Unit = {
    super.pop()
    solver.pop()
  }

  override def foundAnswer(res: Option[Boolean], model: Model = Model.empty, core: Set[Expr] = Set.empty) = {
    super.foundAnswer(res, model, core)

    if (!interrupted && res.isEmpty && model.isEmpty) {
      reporter.ifDebug { debug =>
        debug("Unknown result!?")
      }
    }
  }

  override def reset(): Unit = {
    underlying.reset()
    super.reset()
  }

  override def interrupt(): Unit = {
    super.interrupt()
    solver.interrupt()
  }

  override def recoverInterrupt(): Unit = {
    solver.recoverInterrupt()
    super.recoverInterrupt()
  }
}
