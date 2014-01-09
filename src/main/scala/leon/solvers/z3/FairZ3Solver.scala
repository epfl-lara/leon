/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers.z3

import leon.utils._

import z3.scala._

import leon.solvers._

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.HOTreeOps._
import purescala.TypeTreeOps._

import evaluators._

import termination._

import scala.collection.mutable.{Map => MutableMap}
import scala.collection.mutable.{Set => MutableSet}

object FairZ3Solver {
  def factory(ctx: LeonContext, prog: Program): SolverFactory[FairZ3Solver] = {
    SolverFactory(cond => new FairZ3Solver(ctx, prog, cond))
  }

  def factory(ctx: LeonContext, prog: Program, timeout: Long): SolverFactory[FairZ3Solver] = {
    SolverFactory(cond => new FairZ3Solver(ctx, prog, cond).setTimeout(timeout))
  }
}

class FairZ3Solver(val context : LeonContext, val program: Program, val precondition: Expr)
  extends AbstractZ3Solver
     with Z3ModelReconstruction
     with FairZ3Component {

  enclosing =>

  val (feelingLucky, checkModels, useCodeGen, evalGroundApps, unrollUnsatCores) = locally {
    var lucky            = false
    var check            = false
    var codegen          = false
    var evalground       = false
    var unrollUnsatCores = false

    for(opt <- context.options) opt match {
      case LeonFlagOption("checkmodels", v)        => check            = v
      case LeonFlagOption("feelinglucky", v)       => lucky            = v
      case LeonFlagOption("codegen", v)            => codegen          = v
      case LeonFlagOption("evalground", v)         => evalground       = v
      case LeonFlagOption("fairz3:unrollcores", v) => unrollUnsatCores = v
      case _ =>
    }

    (lucky, check, codegen, evalground, unrollUnsatCores)
  }

  // This is fixed.
  protected[leon] val z3cfg = new Z3Config(
    "MODEL" -> true,
    "TYPE_CHECK" -> true,
    "WELL_SORTED_CHECK" -> true
  )
  toggleWarningMessages(true)

  private def validateModel(model: Z3Model, formula: Expr, variables: Set[Identifier], silenceErrors: Boolean) : (Boolean, Map[Identifier,Expr]) = {
    if(!interrupted) {

      val functionsModel: Map[Z3FuncDecl, (Seq[(Seq[Z3AST], Z3AST)], Z3AST)] = model.getModelFuncInterpretations.map(i => (i._1, (i._2, i._3))).toMap
      val functionsAsMap: Map[Identifier, Expr] = functionsModel.flatMap(p => {
        if(isKnownDecl(p._1)) {
          val tfd = functionDeclToDef(p._1)
          if(!tfd.hasImplementation) {
            val (cses, default) = p._2 
            val ite = cses.foldLeft(fromZ3Formula(model, default, Some(tfd.returnType)))((expr, q) => IfExpr(
                            And(
                              q._1.zip(tfd.args).map(a12 => Equals(fromZ3Formula(model, a12._1, Some(a12._2.tpe)), Variable(a12._2.id)))
                            ),
                            fromZ3Formula(model, q._2, Some(tfd.returnType)),
                            expr))
            Seq((tfd.id, ite))
          } else Seq()
        } else Seq()
      }).toMap
      val constantFunctionsAsMap: Map[Identifier, Expr] = model.getModelConstantInterpretations.flatMap(p => {
        if(isKnownDecl(p._1)) {
          val tfd = functionDeclToDef(p._1)
          if(!tfd.hasImplementation) {
            Seq((tfd.id, fromZ3Formula(model, p._2, Some(tfd.returnType))))
          } else Seq()
        } else Seq()
      }).toMap

      val asMap = modelToMap(model, variables) ++ functionsAsMap ++ constantFunctionsAsMap
      lazy val modelAsString = asMap.toList.map(p => p._1 + " -> " + p._2).mkString("\n")
      val evalResult = evaluator.eval(formula, asMap)

      evalResult match {
        case EvaluationResults.Successful(BooleanLiteral(true)) =>
          reporter.debug("- Model validated.")
          (true, asMap)

        case EvaluationResults.Successful(BooleanLiteral(false)) =>
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

  initZ3()

  private val evaluator : Evaluator = if(useCodeGen) {
      new CodeGenEvaluator(context, program)
    } else {
      new DefaultEvaluator(context, program)
    }

  protected val grounder : Option[GroundEvaluator[Z3AST]] = if (!evalGroundApps) None else Some(new GroundEvaluator[Z3AST] {
    def eval(funDef : TypedFunDef, args : Seq[Z3AST]) : Option[Z3AST] = {
      val ga = args.view.map(asGround)
      if (ga.exists(!_.isDefined)) None else {
        val leonArgs = ga.map(_.get).force
        val (fdArgs, appArgs) = leonArgs.splitAt(funDef.args.size)
        val expr = buildApplication(FunctionInvocation(funDef.fd, fdArgs), appArgs)
        evaluator.eval(expr) match {
          case EvaluationResults.Successful(result) =>
            def application(ast : Z3AST, tpe: TypeTree, args: Seq[Z3AST]): Z3AST = tpe match {
              case FunctionType(argTypes, retType) =>
                val tupleType = TupleType(argTypes)
                typeToSort(tupleType) // make sure tuple type exists
                val constructor = tupleConstructors(tupleType)
                val (appArgs, restArgs) = args.splitAt(argTypes.size)
                application(z3.mkSelect(ast, constructor(appArgs : _*)), retType, restArgs)
              case _ => ast
            }
            val (z3FdArgs, z3AppArgs) = args.splitAt(funDef.args.size)
            val z3Invocation = application(z3.mkApp(functionDefToDecl(funDef), z3FdArgs : _*), funDef.returnType, z3AppArgs)
            val z3Value = toZ3Formula(result).get
            Some(z3.mkEq(z3Invocation, z3Value))
          case _ => throw new Exception("Ground term evaluation should succeed.")
        }
      }
    }
  })

  override protected[leon] def restartZ3(asserted: Seq[Expr]) {
    unrollingBank.reset()

    varsInVC = Set.empty
    frameExpressions = List(Nil)
    
    super.restartZ3(asserted)
  }

  class UnrollingBank() {
    // Keep which function invocation is guarded by which guard,
    // also specify the generation of the blocker.

    private var blockersInfoStack : List[MutableMap[Z3AST,(Int,Int,Z3AST,Set[Invocation[Z3AST]])]] = List(MutableMap())

    def reset() {
      blockersInfoStack = List(MutableMap())
    }

    def blockersInfo = blockersInfoStack.head

    // Note that this computes cumulated sets.
    private var unlockedStack : List[MutableSet[Z3AST]] = List(MutableSet())
    def unlockedSet : MutableSet[Z3AST] = unlockedStack.head
    def wasUnlocked(id : Z3AST) : Boolean = unlockedStack.head(id)

    def push() {
      blockersInfoStack = (MutableMap() ++ blockersInfo) :: blockersInfoStack
      unlockedStack     = (MutableSet() ++ unlockedStack.head) :: unlockedStack
    }

    def pop(lvl: Int) {
      blockersInfoStack = blockersInfoStack.drop(lvl)
      unlockedStack     = unlockedStack.drop(lvl)
    }

    def z3CurrentZ3Blockers = blockersInfo.map(_._2._3)

    def dumpBlockers = {
      blockersInfo.groupBy(_._2._1).toSeq.sortBy(_._1).foreach { case (gen, entries) =>
        reporter.debug("--- "+gen)

        for (((bast), (gen, origGen, ast, fis)) <- entries) {
          reporter.debug(".     "+bast +" ~> "+fis.map(_.fd))
        }
      }
    }

    def canUnroll = !blockersInfo.isEmpty

    def getZ3BlockersToUnlock: Seq[Z3AST] = {
      if (!blockersInfo.isEmpty) {
        val minGeneration = blockersInfo.values.map(_._1).min

        blockersInfo.filter(_._2._1 == minGeneration).toSeq.map(_._1)
      } else {
        Seq()
      }
    }

    private def registerBlocker(gen: Int, id: Z3AST, fis: Set[Invocation[Z3AST]]) {
      if (!wasUnlocked(id)) {
        val z3ast = z3.mkNot(id)
        blockersInfo.get(id) match {
          case Some((exGen, origGen, _, exFis)) =>
            // PS: when recycling `b`s, this assertion becomes dangerous.
            // It's better to simply take the max of the generations.
            // assert(exGen == gen, "Mixing the same id "+id+" with various generations "+ exGen+" and "+gen)

            val maxGen = gen max exGen

            blockersInfo(id) = ((maxGen, origGen, z3ast, fis++exFis))
          case None =>
            blockersInfo(id) = ((gen, gen, z3ast, fis))
        }
      }
    }

    def scanForNewTemplates(expr: Expr): Seq[Z3AST] = {
      // OK, now this is subtle. This `getTemplate` will return
      // a template for a "fake" function. Now, this template will
      // define an activating boolean...
      val template = templates.getTemplate(expr)

      val z3args = for (vd <- template.funDef.args) yield {
        exprToZ3Id.get(Variable(vd.id)) match {
          case Some(ast) =>
            ast
          case None =>
            val ast = templates.encode(vd.id)
            exprToZ3Id += Variable(vd.id) -> ast
            z3IdToExpr += ast -> Variable(vd.id)
            ast
        }
      }

      // ...now this template defines clauses that are all guarded
      // by that activating boolean. If that activating boolean is 
      // undefined (or false) these clauses have no effect...
      val (newClauses, newBlocks) = template.instantiate(template.fActivatingBool, z3args)

      //println(newClauses.mkString("\n"))

      for((i, fis) <- newBlocks) {
        registerBlocker(nextGeneration(0), i, fis)
      }
      
      // ...so we must force it to true!
      template.fActivatingBool +: newClauses
    }

    def nextGeneration(gen: Int) = gen + 3

    def decreaseAllGenerations() = {
      for ((block, (gen, origGen, ast, finvs)) <- blockersInfo) {
        // We also decrease the original generation here
        blockersInfo(block) = (math.max(1,gen-1), math.max(1,origGen-1), ast, finvs)
      }
    }

    def promoteBlocker(b: Z3AST) = {
      if (blockersInfo contains b) {
        val (gen, origGen, ast, finvs) = blockersInfo(b)
        blockersInfo(b) = (1, origGen, ast, finvs)
      }
    }

    def unlock(id: Z3AST) : Seq[Z3AST] = {
      assert(blockersInfo contains id)
      assert(!wasUnlocked(id))

      val (gen, origGen, _, fis) = blockersInfo(id)

      blockersInfo -= id

      var newClauses : Seq[Z3AST] = Seq.empty

      var reintroducedSelf : Boolean = false

      for(fi <- fis) {
        val template              = templates.getTemplate(fi.fd)
        val (newExprs, newBlocks) = template.instantiate(id, fi.args)

        for((i, fis2) <- newBlocks) {
          registerBlocker(nextGeneration(gen), i, fis2)
          if(i == id) {
            reintroducedSelf = true
          }
        }

        newClauses ++= newExprs
      }

      if(!reintroducedSelf) {
        unlockedSet += id
      }

      //println(newClauses.mkString("\n"))
      newClauses
    }
  }

  /*
  for(funDef <- program.functions) {
    if (funDef.fd.annotations.contains("axiomatize") && !axiomatizedFunctions(funDef.fd)) {
      reporter.warning("Function " + funDef.id + " was marked for axiomatization but could not be handled.")
    }
  }
  */

  private var varsInVC = Set[Identifier]()

  private var frameExpressions = List[List[Expr]](Nil)

  val unrollingBank = new UnrollingBank()

  def push() {
    solver.push()
    unrollingBank.push()
    frameExpressions = Nil :: frameExpressions
  }

  def pop(lvl: Int = 1) {
    solver.pop(lvl)
    unrollingBank.pop(lvl)
    frameExpressions = frameExpressions.drop(lvl)
  }

  def innerCheck: Option[Boolean] = {
    fairCheck(Set())
  }

  def innerCheckAssumptions(assumptions: Set[Expr]): Option[Boolean] = {
    fairCheck(assumptions)
  }

  var foundDefinitiveAnswer = false
  var definitiveAnswer : Option[Boolean] = None
  var definitiveModel  : Map[Identifier,Expr] = Map.empty
  var definitiveCore   : Set[Expr] = Set.empty

  protected def assertZ3Cnstr(expression: Expr) {
    varsInVC ++= variablesOf(expression)

    frameExpressions = (expression :: frameExpressions.head) :: frameExpressions.tail

    val newClauses = unrollingBank.scanForNewTemplates(expression)

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

    def entireFormula  = And(assumptions.toSeq ++ frameExpressions.flatten)

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
      core.filter(assumptionsAsZ3Set).map(ast => fromZ3Formula(null, ast, None) match {
          case n @ Not(Variable(_)) => n
          case v @ Variable(_) => v
          case x => scala.sys.error("Impossible element extracted from core: " + ast + " (as Leon tree : " + x + ")")
      }).toSet
    }

    while(!foundDefinitiveAnswer && !interrupted) {

      //val blockingSetAsZ3 : Seq[Z3AST] = blockingSet.toSeq.map(toZ3Formula(_).get)
      // println("Blocking set : " + blockingSet)

      reporter.debug(" - Running Z3 search...")

      reporter.debug("Searching in:\n"+solver.getAssertions.toSeq.mkString("\nAND\n"))
      reporter.debug("Unroll.  Assumptions:\n"+unrollingBank.z3CurrentZ3Blockers.mkString("  &&  "))
      reporter.debug("Userland Assumptions:\n"+assumptionsAsZ3.mkString("  &&  "))

      // println(solver.getAssertions.mkString("\n"))
      // println()

      solver.push() // FIXME: remove when z3 bug is fixed
      val res = solver.checkAssumptions((assumptionsAsZ3 ++ unrollingBank.z3CurrentZ3Blockers) :_*)
      solver.pop()  // FIXME: remove when z3 bug is fixed

      reporter.debug(" - Finished search with blocked literals")

      res match {
        case None =>
          reporter.ifDebug { debug => 
            if (solver.getReasonUnknown != "canceled") {
              debug("Z3 returned unknown: " + solver.getReasonUnknown)
            }
          }
          foundAnswer(None)

        case Some(true) => // SAT

          val z3model = solver.getModel

          if (this.checkModels) {
            val (isValid, model) = validateModel(z3model, entireFormula, varsInVC, silenceErrors = false)

            if (isValid) {
              foundAnswer(Some(true), model)
            } else {
              reporter.error("Something went wrong. The model should have been valid, yet we got this : ")
              reporter.error(model)
              foundAnswer(None, model)
            }
          } else {
            val model = modelToMap(z3model, varsInVC)

            //lazy val modelAsString = model.toList.map(p => p._1 + " -> " + p._2).mkString("\n")
            //reporter.debug("- Found a model:")
            //reporter.debug(modelAsString)

            foundAnswer(Some(true), model)
          }

        case Some(false) if !unrollingBank.canUnroll =>

          val core = z3CoreToCore(solver.getUnsatCore)

          foundAnswer(Some(false), core = core)

        // This branch is both for with and without unsat cores. The
        // distinction is made inside.
        case Some(false) =>

          val z3Core = solver.getUnsatCore

          def coreElemToBlocker(c: Z3AST): (Z3AST, Boolean) = {
            z3.getASTKind(c) match {
              case Z3AppAST(decl, args) =>
                z3.getDeclKind(decl) match {
                  case Z3DeclKind.OpNot =>
                    (args(0), true)
                  case Z3DeclKind.OpUninterpreted =>
                    (c, false)
                }

              case ast =>
                (c, false)
            }
          }

          if (unrollUnsatCores) {
            unrollingBank.decreaseAllGenerations()

            for (c <- solver.getUnsatCore) {
              val (z3ast, pol) = coreElemToBlocker(c)
              assert(pol == true)

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

            solver.push() // FIXME: remove when z3 bug is fixed
            val res2 = solver.checkAssumptions(assumptionsAsZ3 : _*)
            solver.pop()  // FIXME: remove when z3 bug is fixed

            res2 match {
              case Some(false) =>
                //reporter.debug("UNSAT WITHOUT Blockers")
                foundAnswer(Some(false), core = z3CoreToCore(solver.getUnsatCore))
              case Some(true) =>
                //reporter.debug("SAT WITHOUT Blockers")
                if (this.feelingLucky && !interrupted) {
                  // we might have been lucky :D
                  val (wereWeLucky, cleanModel) = validateModel(solver.getModel, entireFormula, varsInVC, silenceErrors = true)

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

            val toRelease = unrollingBank.getZ3BlockersToUnlock

            reporter.debug(" - more unrollings")

            for(id <- toRelease) {
              val newClauses = unrollingBank.unlock(id)

              for(ncl <- newClauses) {
                solver.assertCnstr(ncl)
              }

              reporter.debug(" - finished unrolling")
            }

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
