/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package combinators

import purescala.Printable
import purescala.Common._
import purescala.Definitions._
import purescala.Quantification._
import purescala.Constructors._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import purescala.TypeOps.bestRealType
import utils._

import templates._
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

  override val definedOptions: Set[LeonOptionDef[Any]] =
    Set(optCheckModels, optFeelingLucky, optUseCodeGen, optUnrollCores, optAssumePre, optUnrollFactor, optPartialModels)
}

object UnrollingProcedure extends UnrollingProcedure

trait AbstractUnrollingSolver[T]
  extends UnrollingProcedure
     with Solver
     with EvaluatingSolver
     with QuantificationSolver {

  val unfoldFactor     = context.findOptionOrDefault(optUnrollFactor)
  val feelingLucky     = context.findOptionOrDefault(optFeelingLucky)
  val checkModels      = context.findOptionOrDefault(optCheckModels)
  val useCodeGen       = context.findOptionOrDefault(optUseCodeGen)
  val unrollUnsatCores = context.findOptionOrDefault(optUnrollCores)
  val assumePreHolds   = context.findOptionOrDefault(optAssumePre)
  val partialModels    = context.findOptionOrDefault(optPartialModels)

  protected var foundDefinitiveAnswer = false
  protected var definitiveAnswer : Option[Boolean] = None
  protected var definitiveModel  : Model = Model.empty
  protected var definitiveCore   : Set[Expr] = Set.empty

  def check: Option[Boolean] = {
    genericCheck(Set.empty)
  }

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

  private val freeVars    = new IncrementalMap[Identifier, T]()
  private val constraints = new IncrementalSeq[Expr]()

  protected var interrupted : Boolean = false

  protected val reporter = context.reporter

  lazy val templateGenerator = new TemplateGenerator(templateEncoder, assumePreHolds)
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

  def assertCnstr(expression: Expr, bindings: Map[Identifier, T]): Unit = {
    constraints += expression
    freeVars ++= bindings

    val newClauses = unrollingBank.getClauses(expression, bindings.map { case (k, v) => Variable(k) -> v })
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
    def get(id: Identifier): Option[Expr]
    def eval(elem: T, tpe: TypeTree): Option[Expr]

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

    evaluator.eval(expr, model) match {
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

  private def getPartialModel: HenkinModel = {
    val wrapped = solverGetModel

    val typeInsts = templateGenerator.manager.typeInstantiations
    val partialInsts = templateGenerator.manager.partialInstantiations
    val lambdaInsts = templateGenerator.manager.lambdaInstantiations

    val typeDomains: Map[TypeTree, Set[Seq[Expr]]] = typeInsts.map {
      case (tpe, domain) => tpe -> domain.flatMap { case (b, m) => wrapped.extract(b, m) }.toSet
    }

    val funDomains: Map[Identifier, Set[Seq[Expr]]] = freeVars.map { case (id, idT) =>
      id -> partialInsts.get(idT).toSeq.flatten.flatMap { case (b, m) => wrapped.extract(b, m) }.toSet
    }

    val lambdaDomains: Map[Lambda, Set[Seq[Expr]]] = lambdaInsts.map {
      case (l, domain) => l -> domain.flatMap { case (b, m) => wrapped.extract(b, m) }.toSet
    }

    val model = new Model(freeVars.toMap.map { case (id, _) =>
      val value = wrapped.get(id).getOrElse(simplestValue(id.getType))
      id -> (funDomains.get(id) match {
        case Some(domain) =>
          val FiniteLambda(_, dflt, tpe) = value
          FiniteLambda(domain.toSeq.map { es =>
            val optEv = evaluator.eval(application(value, es)).result
            es -> optEv.getOrElse(scala.sys.error("Unexpectedly failed to evaluate " + application(value, es)))
          }, dflt, tpe)

        case None => postMap {
          case p @ FiniteLambda(mapping, dflt, tpe) =>
            Some(FiniteLambda(typeDomains.get(tpe) match {
              case Some(domain) => domain.toSeq.map { es =>
                val optEv = evaluator.eval(application(value, es)).result
                es -> optEv.getOrElse(scala.sys.error("Unexpectedly failed to evaluate " + application(value, es)))
              }
              case _ => Seq.empty
            }, dflt, tpe))
          case _ => None
        } (value)
      })
    })

    val domains = new HenkinDomains(lambdaDomains, typeDomains)
    new HenkinModel(model.toMap, domains)
  }

  private def getTotalModel: Model = {
    val wrapped = solverGetModel

    val typeInsts = templateGenerator.manager.typeInstantiations
    val partialInsts = templateGenerator.manager.partialInstantiations

    def extractCond(params: Seq[Identifier], args: Seq[(T, Expr)], structure: Map[T, Identifier]): Seq[Expr] = (params, args) match {
      case (id +: rparams, (v, arg) +: rargs) =>
        if (templateGenerator.manager.isQuantifier(v)) {
          structure.get(v) match {
            case Some(pid) => Equals(Variable(id), Variable(pid)) +: extractCond(rparams, rargs, structure)
            case None => extractCond(rparams, rargs, structure + (v -> id))
          }
        } else {
          Equals(Variable(id), arg) +: extractCond(rparams, rargs, structure)
        }
      case _ => Seq.empty
    }

    new Model(freeVars.toMap.map { case (id, idT) =>
      val value = wrapped.get(id).getOrElse(simplestValue(id.getType))
      id -> (id.getType match {
        case FunctionType(from, to) =>
          val params = from.map(tpe => FreshIdentifier("x", tpe, true))
          val domain = partialInsts.get(idT).orElse(typeInsts.get(bestRealType(id.getType))).toSeq.flatten
          val conditionals = domain.flatMap { case (b, m) =>
            wrapped.extract(b, m) match {
              case Some(args) =>
                val result = evaluator.eval(application(value, args)).result.getOrElse {
                  scala.sys.error("Unexpectedly failed to evaluate " + application(value, args))
                }

                val c1 = (params zip args).map(p => Equals(Variable(p._1), p._2))
                if (m.args.exists(arg => templateGenerator.manager.isQuantifier(arg.encoded))) {
                  val c2 = extractCond(params, m.args.map(_.encoded) zip args, Map.empty)
                  Seq(c1 -> result, c2 -> result)
                } else {
                  Seq(c1 -> result)
                }

              case None => Seq.empty
            }
          }

          val filteredConds = conditionals
            .foldLeft(Map.empty[Seq[Expr], Expr]) { case (mapping, (conds, result)) =>
              if (mapping.isDefinedAt(conds)) mapping else mapping + (conds -> result)
            }

          val rest :+ ((_, dflt)) = filteredConds.toSeq.sortBy(_._1.size)
          val body = rest.foldLeft(dflt) { case (elze, (conds, res)) =>
            if (conds.isEmpty) elze else IfExpr(andJoin(conds), res, elze)
          }

          Lambda(params.map(ValDef(_)), body)

        case _ => value
      })
    })
  }

  def genericCheck(assumptions: Set[Expr]): Option[Boolean] = {
    foundDefinitiveAnswer = false

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

    while(!foundDefinitiveAnswer && !interrupted) {
      reporter.debug(" - Running search...")
      var quantify = false

      def check[R](clauses: Seq[T])(block: Option[Boolean] => R) =
        if (partialModels) solverCheckAssumptions(clauses)(block) else solverCheck(clauses)(block)

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
              val clauses = templateGenerator.manager.checkClauses
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
                val valid = !checkModels || validateModel(model, assumptionsSeq, silenceErrors = false)

                if (valid) {
                  foundAnswer(Some(true), model)
                } else {
                  reporter.error("Something went wrong. The model should have been valid, yet we got this : ")
                  reporter.error(model.asString(context))
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
              if (this.feelingLucky && !interrupted) {
                // we might have been lucky :D
                val model = extractModel(solverGetModel)
                val valid = validateModel(model, assumptionsSeq, silenceErrors = true)
                if (valid) foundAnswer(Some(true), model)
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

          val newClauses = unrollingBank.unrollBehind(toRelease)

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

class UnrollingSolver(val context: LeonContext, val program: Program, underlying: Solver)
  extends AbstractUnrollingSolver[Expr] {

  override val name = "U:"+underlying.name

  def free() {
    underlying.free()
  }

  val printable = (e: Expr) => e

  val templateEncoder = new TemplateEncoder[Expr] {
    def encodeId(id: Identifier): Expr= {
      Variable(id.freshen)
    }

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

  val solver = underlying

  def assertCnstr(expression: Expr): Unit = {
    assertCnstr(expression, variablesOf(expression).map(id => id -> id.toVariable).toMap)
  }

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
    def get(id: Identifier): Option[Expr] = model.get(id)
    def eval(elem: Expr, tpe: TypeTree): Option[Expr] = evaluator.eval(elem, model).result
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

    if (!interrupted && res == None && model == None) {
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
