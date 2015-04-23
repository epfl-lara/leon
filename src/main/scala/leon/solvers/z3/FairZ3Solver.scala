/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package z3

import _root_.z3.scala._

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.Constructors._
import purescala.ExprOps._

import solvers.templates._

import evaluators._

import termination._

class FairZ3Solver(val context : LeonContext, val program: Program)
  extends AbstractZ3Solver
     with Z3ModelReconstruction
     with FairZ3Component {

  enclosing =>

  val feelingLucky      = context.findOptionOrDefault(optFeelingLucky)
  val checkModels       = context.findOptionOrDefault(optCheckModels)
  val useCodeGen        = context.findOptionOrDefault(optUseCodeGen)
  val evalGroundApps    = context.findOptionOrDefault(optEvalGround)
  val unrollUnsatCores  = context.findOptionOrDefault(optUnrollCores)

  private val evaluator: Evaluator =
    if(useCodeGen) {
      // TODO If somehow we could not recompile each time we create a solver,
      // that would be good?
      new CodeGenEvaluator(context, program)
    } else {
      new DefaultEvaluator(context, program)
    }

  protected[z3] def getEvaluator : Evaluator = evaluator

  private val terminator : TerminationChecker = new SimpleTerminationChecker(context, program)

  protected[z3] def getTerminator : TerminationChecker = terminator

  // FIXME: Dirty hack to bypass z3lib bug. Assumes context is the same over all instances of FairZ3Solver
  protected[leon] val z3cfg = context.synchronized { new Z3Config(
    "MODEL" -> true,
    "TYPE_CHECK" -> true,
    "WELL_SORTED_CHECK" -> true
  )}
  toggleWarningMessages(true)


  private def validateModel(model: Z3Model, formula: Expr, variables: Set[Identifier], silenceErrors: Boolean) : (Boolean, Map[Identifier,Expr]) = {
    if(!interrupted) {

      val functionsModel: Map[Z3FuncDecl, (Seq[(Seq[Z3AST], Z3AST)], Z3AST)] = model.getModelFuncInterpretations.map(i => (i._1, (i._2, i._3))).toMap
      val functionsAsMap: Map[Identifier, Expr] = functionsModel.flatMap(p => {
        if (functions containsZ3 p._1) {
          val tfd = functions.toLeon(p._1)
          if (!tfd.hasImplementation) {
            val (cses, default) = p._2
            val ite = cses.foldLeft(fromZ3Formula(model, default))((expr, q) => IfExpr(
              andJoin(
                q._1.zip(tfd.params).map(a12 => Equals(fromZ3Formula(model, a12._1), Variable(a12._2.id)))
              ),
              fromZ3Formula(model, q._2),
              expr))
            Seq((tfd.id, ite))
          } else Seq()
        } else Seq()
      })

      val constantFunctionsAsMap: Map[Identifier, Expr] = model.getModelConstantInterpretations.flatMap(p => {
        if(functions containsZ3 p._1) {
          val tfd = functions.toLeon(p._1)
          if(!tfd.hasImplementation) {
            Seq((tfd.id, fromZ3Formula(model, p._2)))
          } else Seq()
        } else Seq()
      }).toMap

      val asMap = modelToMap(model, variables) ++ functionsAsMap ++ constantFunctionsAsMap
      val evalResult = evaluator.eval(formula, asMap)

      evalResult match {
        case EvaluationResults.Successful(BooleanLiteral(true)) =>
          reporter.debug("- Model validated.")
          (true, asMap)

        case EvaluationResults.Successful(res) =>
          assert(res == BooleanLiteral(false), "Checking model returned non-boolean")
          reporter.debug("- Invalid model.")
          (false, asMap)

        case EvaluationResults.RuntimeError(msg) =>
          reporter.debug("- Model leads to runtime error.")
          (false, asMap)

        case EvaluationResults.EvaluatorError(msg) => 
          if (silenceErrors) {
            reporter.debug("- Model leads to evaluator error: " + msg)
          } else {
            reporter.warning("Something went wrong. While evaluating the model, we got this : " + msg)
          }
          (false, asMap)

      }
    } else {
      (false, Map.empty)
    }
  }

  val templateGenerator = new TemplateGenerator(new TemplateEncoder[Z3AST] {
    def encodeId(id: Identifier): Z3AST = {
      idToFreshZ3Id(id)
    }

    def encodeExpr(bindings: Map[Identifier, Z3AST])(e: Expr): Z3AST = {
      toZ3Formula(e, bindings).getOrElse {
        reporter.fatalError("Failed to translate "+e+" to z3 ("+e.getClass+")")
      }
    }

    def substitute(substMap: Map[Z3AST, Z3AST]): Z3AST => Z3AST = {
      val (from, to) = substMap.unzip
      val (fromArray, toArray) = (from.toArray, to.toArray)

      (c: Z3AST) => z3.substitute(c, fromArray, toArray)
    }

    def mkNot(e: Z3AST) = z3.mkNot(e)
    def mkOr(es: Z3AST*) = z3.mkOr(es : _*)
    def mkAnd(es: Z3AST*) = z3.mkAnd(es : _*)
    def mkEquals(l: Z3AST, r: Z3AST) = z3.mkEq(l, r)
    def mkImplies(l: Z3AST, r: Z3AST) = z3.mkImplies(l, r)
  })


  initZ3()

  val solver = z3.mkSolver()

  private var varsInVC = List[Set[Identifier]](Set())

  private var frameExpressions = List[List[Expr]](Nil)

  val unrollingBank = new UnrollingBank(reporter, templateGenerator)

  def push() {
    solver.push()
    unrollingBank.push()
    varsInVC = Set[Identifier]() :: varsInVC
    frameExpressions = Nil :: frameExpressions
  }

  def pop(lvl: Int = 1) {
    solver.pop(lvl)
    unrollingBank.pop(lvl)
    varsInVC = varsInVC.drop(lvl)
    frameExpressions = frameExpressions.drop(lvl)
  }

  override def check: Option[Boolean] = {
    fairCheck(Set())
  }

  override def checkAssumptions(assumptions: Set[Expr]): Option[Boolean] = {
    fairCheck(assumptions)
  }

  var foundDefinitiveAnswer = false
  var definitiveAnswer : Option[Boolean] = None
  var definitiveModel  : Map[Identifier,Expr] = Map.empty
  var definitiveCore   : Set[Expr] = Set.empty

  def assertCnstr(expression: Expr) {
    val freeVars = variablesOf(expression)
    varsInVC = (varsInVC.head ++ freeVars) :: varsInVC.tail

    // We make sure all free variables are registered as variables
    freeVars.foreach { v =>
      variables.toZ3OrCompute(Variable(v)) {
        templateGenerator.encoder.encodeId(v)
      }
    }

    frameExpressions = (expression :: frameExpressions.head) :: frameExpressions.tail

    val newClauses = unrollingBank.getClauses(expression, variables.leonToZ3)

    for (cl <- newClauses) {
      solver.assertCnstr(cl)
    }
  }

  def getModel = {
    definitiveModel
  }

  def getUnsatCore = {
    definitiveCore
  }

  def fairCheck(assumptions: Set[Expr]): Option[Boolean] = {
    foundDefinitiveAnswer = false

    def entireFormula  = andJoin(assumptions.toSeq ++ frameExpressions.flatten)

    def foundAnswer(answer : Option[Boolean], model : Map[Identifier,Expr] = Map.empty, core: Set[Expr] = Set.empty) : Unit = {
      foundDefinitiveAnswer = true
      definitiveAnswer = answer
      definitiveModel  = model
      definitiveCore   = core
    }

    // these are the optional sequence of assumption literals
    val assumptionsAsZ3: Seq[Z3AST]    = assumptions.flatMap(toZ3Formula(_)).toSeq
    val assumptionsAsZ3Set: Set[Z3AST] = assumptionsAsZ3.toSet

    def z3CoreToCore(core: Seq[Z3AST]): Set[Expr] = {
      core.filter(assumptionsAsZ3Set).map(ast => fromZ3Formula(null, ast) match {
          case n @ Not(Variable(_)) => n
          case v @ Variable(_) => v
          case x => scala.sys.error("Impossible element extracted from core: " + ast + " (as Leon tree : " + x + ")")
      }).toSet
    }

    while(!foundDefinitiveAnswer && !interrupted) {

      //val blockingSetAsZ3 : Seq[Z3AST] = blockingSet.toSeq.map(toZ3Formula(_).get)
      // println("Blocking set : " + blockingSet)

      reporter.debug(" - Running Z3 search...")

      //reporter.debug("Searching in:\n"+solver.getAssertions.toSeq.mkString("\nAND\n"))
      //reporter.debug("Unroll.  Assumptions:\n"+unrollingBank.z3CurrentZ3Blockers.mkString("  &&  "))
      //reporter.debug("Userland Assumptions:\n"+assumptionsAsZ3.mkString("  &&  "))

      val timer = context.timers.solvers.z3.check.start()
      solver.push() // FIXME: remove when z3 bug is fixed
      val res = solver.checkAssumptions((assumptionsAsZ3 ++ unrollingBank.currentBlockers) :_*)
      solver.pop()  // FIXME: remove when z3 bug is fixed
      timer.stop()

      reporter.debug(" - Finished search with blocked literals")

      lazy val allVars = varsInVC.flatten.toSet

      res match {
        case None =>
          reporter.ifDebug { debug => 
            if (solver.getReasonUnknown != "canceled") {
              debug("Z3 returned unknown: " + solver.getReasonUnknown)
            }
          }
          foundAnswer(None)

        case Some(true) => // SAT

          val z3model = solver.getModel()

          if (this.checkModels) {
            val (isValid, model) = validateModel(z3model, entireFormula, allVars, silenceErrors = false)

            if (isValid) {
              foundAnswer(Some(true), model)
            } else {
              reporter.error("Something went wrong. The model should have been valid, yet we got this : ")
              reporter.error(model)
              foundAnswer(None, model)
            }
          } else {
            val model = modelToMap(z3model, allVars)

            //lazy val modelAsString = model.toList.map(p => p._1 + " -> " + p._2).mkString("\n")
            //reporter.debug("- Found a model:")
            //reporter.debug(modelAsString)

            foundAnswer(Some(true), model)
          }

        case Some(false) if !unrollingBank.canUnroll =>

          val core = z3CoreToCore(solver.getUnsatCore())

          foundAnswer(Some(false), core = core)

        // This branch is both for with and without unsat cores. The
        // distinction is made inside.
        case Some(false) =>

          //@mk this seems to be dead code
          val z3Core = solver.getUnsatCore()

          def coreElemToBlocker(c: Z3AST): (Z3AST, Boolean) = {
            z3.getASTKind(c) match {
              case Z3AppAST(decl, args) =>
                z3.getDeclKind(decl) match {
                  case Z3DeclKind.OpNot =>
                    (args.head, true)
                  case Z3DeclKind.OpUninterpreted =>
                    (c, false)
                }

              case ast =>
                (c, false)
            }
          }

          if (unrollUnsatCores) {
            unrollingBank.decreaseAllGenerations()

            for (c <- solver.getUnsatCore()) {
              val (z3ast, pol) = coreElemToBlocker(c)
              assert(pol)

              unrollingBank.promoteBlocker(z3ast)
            }

          }

          //debug("UNSAT BECAUSE: "+solver.getUnsatCore.mkString("\n  AND  \n"))
          //debug("UNSAT BECAUSE: "+core.mkString("  AND  "))

          if (!interrupted) {
            if (this.feelingLucky) {
              // we need the model to perform the additional test
              reporter.debug(" - Running search without blocked literals (w/ lucky test)")
            } else {
              reporter.debug(" - Running search without blocked literals (w/o lucky test)")
            }

            val timer = context.timers.solvers.z3.check.start()
            solver.push() // FIXME: remove when z3 bug is fixed
            val res2 = solver.checkAssumptions(assumptionsAsZ3 : _*)
            solver.pop()  // FIXME: remove when z3 bug is fixed
            timer.stop()

            res2 match {
              case Some(false) =>
                //reporter.debug("UNSAT WITHOUT Blockers")
                foundAnswer(Some(false), core = z3CoreToCore(solver.getUnsatCore))
              case Some(true) =>
                //reporter.debug("SAT WITHOUT Blockers")
                if (this.feelingLucky && !interrupted) {
                  // we might have been lucky :D
                  val (wereWeLucky, cleanModel) = validateModel(solver.getModel, entireFormula, allVars, silenceErrors = true)

                  if(wereWeLucky) {
                    foundAnswer(Some(true), cleanModel)
                  }
                }

              case None =>
                foundAnswer(None)
            }
          }

          if(interrupted) {
            foundAnswer(None)
          }

          if(!foundDefinitiveAnswer) { 
            reporter.debug("- We need to keep going.")

            val toRelease = unrollingBank.getBlockersToUnlock

            reporter.debug(" - more unrollings")

            val newClauses = unrollingBank.unrollBehind(toRelease)

            for(ncl <- newClauses) {
              solver.assertCnstr(ncl)
            }

            //readLine()

            reporter.debug(" - finished unrolling")
          }
      }
    }

    if(interrupted) {
      None
    } else {
      definitiveAnswer
    }
  }
}
