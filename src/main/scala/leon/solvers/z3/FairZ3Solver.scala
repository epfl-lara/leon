/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers.z3

import z3.scala._

import leon.solvers.Solver

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._

import evaluators._

import termination._

import scala.collection.mutable.{Map => MutableMap}
import scala.collection.mutable.{Set => MutableSet}

class FairZ3Solver(context : LeonContext)
  extends Solver(context)
     with AbstractZ3Solver
     with Z3ModelReconstruction 
     with LeonComponent {

  enclosing =>

  val name = "Z3-f"
  val description = "Fair Z3 Solver"

  override val definedOptions : Set[LeonOptionDef] = Set(
    LeonFlagOptionDef("evalground",         "--evalground",         "Use evaluator on functions applied to ground arguments"),
    LeonFlagOptionDef("checkmodels",        "--checkmodels",        "Double-check counter-examples with evaluator"),
    LeonFlagOptionDef("feelinglucky",       "--feelinglucky",       "Use evaluator to find counter-examples early"),
    LeonFlagOptionDef("codegen",            "--codegen",            "Use compiled evaluator instead of interpreter"),
    LeonFlagOptionDef("fairz3:unrollcores", "--fairz3:unrollcores", "Use unsat-cores to drive unrolling while remaining fair")
  )

  // What wouldn't we do to avoid defining vars?
  val (feelingLucky, checkModels, useCodeGen, evalGroundApps, unrollUnsatCores) = locally {
    var lucky            = false
    var check            = false
    var codegen          = false
    var evalground       = false
    var unrollUnsatCores = false

    for(opt <- context.options) opt match {
      case LeonFlagOption("checkmodels")        => check            = true
      case LeonFlagOption("feelinglucky")       => lucky            = true
      case LeonFlagOption("codegen")            => codegen          = true
      case LeonFlagOption("evalground")         => evalground       = true
      case LeonFlagOption("fairz3:unrollcores") => unrollUnsatCores = true
      case _ =>
    }

    (lucky, check, codegen, evalground, unrollUnsatCores)
  }

  private var evaluator : Evaluator = null
  protected[z3] def getEvaluator : Evaluator = evaluator

  private var terminator : TerminationChecker = null
  protected[z3] def getTerminator : TerminationChecker = terminator

  override def setProgram(prog : Program) {
    super.setProgram(prog)

    evaluator = if(useCodeGen) {
      // TODO If somehow we could not recompile each time we create a solver,
      // that would be good?
      new CodeGenEvaluator(context, prog)
    } else {
      new DefaultEvaluator(context, prog)
    }

    terminator = new SimpleTerminationChecker(context, prog)
  }

  // This is fixed.
  protected[leon] val z3cfg = new Z3Config(
    "MODEL" -> true,
    "MBQI" -> false,
    "TYPE_CHECK" -> true,
    "WELL_SORTED_CHECK" -> true
  )
  toggleWarningMessages(true)

  def isKnownDef(funDef: FunDef) : Boolean = functionMap.isDefinedAt(funDef)
  
  def functionDefToDecl(funDef: FunDef) : Z3FuncDecl = 
      functionMap.getOrElse(funDef, scala.sys.error("No Z3 definition found for function symbol " + funDef.id.name + "."))

  def isKnownDecl(decl: Z3FuncDecl) : Boolean = reverseFunctionMap.isDefinedAt(decl)
  
  def functionDeclToDef(decl: Z3FuncDecl) : FunDef = 
      reverseFunctionMap.getOrElse(decl, scala.sys.error("No FunDef corresponds to Z3 definition " + decl + "."))

  private var functionMap: Map[FunDef, Z3FuncDecl] = Map.empty
  private var reverseFunctionMap: Map[Z3FuncDecl, FunDef] = Map.empty
  private var axiomatizedFunctions : Set[FunDef] = Set.empty

  protected[leon] def prepareFunctions: Unit = {
    functionMap = Map.empty
    reverseFunctionMap = Map.empty
    for (funDef <- program.definedFunctions) {
      val sortSeq = funDef.args.map(vd => typeToSort(vd.tpe))
      val returnSort = typeToSort(funDef.returnType)

      val z3Decl = z3.mkFreshFuncDecl(funDef.id.name, sortSeq, returnSort)
      functionMap = functionMap + (funDef -> z3Decl)
      reverseFunctionMap = reverseFunctionMap + (z3Decl -> funDef)
    }
  }

  override def solve(vc: Expr) = {
    val solver = getNewSolver
    solver.assertCnstr(Not(vc))
    solver.check.map(!_)
  }

  override def solveSAT(vc : Expr) : (Option[Boolean],Map[Identifier,Expr]) = {
    val solver = getNewSolver
    solver.assertCnstr(vc)
    (solver.check, solver.getModel)
  }

  override def halt() {
    super.halt
    if(z3 ne null) {
      z3.interrupt
    }
  }

  override def solveSATWithCores(expression: Expr, assumptions: Set[Expr]): (Option[Boolean], Map[Identifier, Expr], Set[Expr]) = {
    val solver = getNewSolver
    solver.assertCnstr(expression)
    (solver.checkAssumptions(assumptions), solver.getModel, solver.getUnsatCore)
  }

  private def validateModel(model: Z3Model, formula: Expr, variables: Set[Identifier], silenceErrors: Boolean) : (Boolean, Map[Identifier,Expr]) = {
    if(!forceStop) {

      val functionsModel: Map[Z3FuncDecl, (Seq[(Seq[Z3AST], Z3AST)], Z3AST)] = model.getModelFuncInterpretations.map(i => (i._1, (i._2, i._3))).toMap
      val functionsAsMap: Map[Identifier, Expr] = functionsModel.flatMap(p => {
        if(isKnownDecl(p._1)) {
          val fd = functionDeclToDef(p._1)
          if(!fd.hasImplementation) {
            val (cses, default) = p._2 
            val ite = cses.foldLeft(fromZ3Formula(model, default, Some(fd.returnType)))((expr, q) => IfExpr(
                            And(
                              q._1.zip(fd.args).map(a12 => Equals(fromZ3Formula(model, a12._1, Some(a12._2.tpe)), Variable(a12._2.id)))
                            ),
                            fromZ3Formula(model, q._2, Some(fd.returnType)),
                            expr))
            Seq((fd.id, ite))
          } else Seq()
        } else Seq()
      }).toMap
      val constantFunctionsAsMap: Map[Identifier, Expr] = model.getModelConstantInterpretations.flatMap(p => {
        if(isKnownDecl(p._1)) {
          val fd = functionDeclToDef(p._1)
          if(!fd.hasImplementation) {
            Seq((fd.id, fromZ3Formula(model, p._2, Some(fd.returnType))))
          } else Seq()
        } else Seq()
      }).toMap

      val asMap = modelToMap(model, variables) ++ functionsAsMap ++ constantFunctionsAsMap
      lazy val modelAsString = asMap.toList.map(p => p._1 + " -> " + p._2).mkString("\n")
      val evalResult = evaluator.eval(formula, asMap)

      evalResult match {
        case EvaluationResults.Successful(BooleanLiteral(true)) =>
          reporter.info("- Model validated.")
          (true, asMap)

        case EvaluationResults.Successful(BooleanLiteral(false)) =>
          reporter.info("- Invalid model.")
          (false, asMap)

        case EvaluationResults.RuntimeError(msg) =>
          reporter.info("- Model leads to runtime error.")
          (false, asMap)

        case EvaluationResults.EvaluatorError(msg) => 
          if (silenceErrors) {
            reporter.info("- Model leads to evaluator error: " + msg)
          } else {
            reporter.warning("Something went wrong. While evaluating the model, we got this : " + msg)
          }
          (false, asMap)

      }
    } else {
      (false, Map.empty)
    }
  }

  private val funDefTemplateCache : MutableMap[FunDef, FunctionTemplate] = MutableMap.empty
  private val exprTemplateCache   : MutableMap[Expr  , FunctionTemplate] = MutableMap.empty

  private def getTemplate(funDef: FunDef): FunctionTemplate = {
    funDefTemplateCache.getOrElse(funDef, {
      val res = FunctionTemplate.mkTemplate(this, funDef, true)
      funDefTemplateCache += funDef -> res
      res
    })
  }

  private def getTemplate(body: Expr): FunctionTemplate = {
    exprTemplateCache.getOrElse(body, {
      val fakeFunDef = new FunDef(FreshIdentifier("fake", true), body.getType, variablesOf(body).toSeq.map(id => VarDecl(id, id.getType)))
      fakeFunDef.body = Some(body)

      val res = FunctionTemplate.mkTemplate(this, fakeFunDef, false)
      exprTemplateCache += body -> res
      res
    })
  }

  class UnrollingBank {
    // Keep which function invocation is guarded by which guard,
    // also specify the generation of the blocker.

    private var blockersInfoStack : List[MutableMap[Z3AST,(Int,Int,Z3AST,Set[Z3FunctionInvocation])]] = List(MutableMap())

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
        reporter.info("--- "+gen)

        for (((bast), (gen, origGen, ast, fis)) <- entries) {
          reporter.info(".     "+bast +" ~> "+fis.map(_.funDef.id))
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

    private def registerBlocker(gen: Int, id: Z3AST, fis: Set[Z3FunctionInvocation]) {
      val z3ast = z3.mkNot(id)
      blockersInfo.get(id) match {
        case Some((exGen, origGen, _, exFis)) =>
          // PS: when recycling `b`s, this assertion becomes dangerous.
          // It's better to simply take the min of the generations.
          // assert(exGen == gen, "Mixing the same id "+id+" with various generations "+ exGen+" and "+gen)

          val minGen = gen max exGen

          blockersInfo(id) = ((minGen, origGen, z3ast, fis++exFis))
        case None =>
          blockersInfo(id) = ((gen, gen, z3ast, fis))
      }
    }

    def scanForNewTemplates(expr: Expr): Seq[Z3AST] = {
      // OK, now this is subtle. This `getTemplate` will return
      // a template for a "fake" function. Now, this template will
      // define an activating boolean...
      val template = getTemplate(expr)

      val z3args = for (vd <- template.funDef.args) yield {
        exprToZ3Id.get(Variable(vd.id)) match {
          case Some(ast) =>
            ast
          case None =>
            val ast = idToFreshZ3Id(vd.id)
            exprToZ3Id += Variable(vd.id) -> ast
            z3IdToExpr += ast -> Variable(vd.id)
            ast
        }
      }

      // ...now this template defines clauses that are all guarded
      // by that activating boolean. If that activating boolean is 
      // undefined (or false) these clauses have no effect...
      val (newClauses, newBlocks) =
        template.instantiate(template.z3ActivatingBool, z3args)

      for((i, fis) <- newBlocks) {
        registerBlocker(nextGeneration(0), i, fis)
      }
      
      // ...so we must force it to true!
      template.z3ActivatingBool +: newClauses
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

      if(unlockedSet(id)) return Seq.empty

      val (gen, origGen, _, fis) = blockersInfo(id)

      blockersInfo -= id
      val twice = wasUnlocked(id)

      var newClauses : Seq[Z3AST] = Seq.empty

      var reintroducedSelf : Boolean = false

      for(fi <- fis) {
        val template              = getTemplate(fi.funDef)
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

      newClauses
    }
  }

  def getNewSolver = new solvers.IncrementalSolver {
    private val evaluator    = enclosing.evaluator
    private val feelingLucky = enclosing.feelingLucky
    private val checkModels  = enclosing.checkModels
    private val useCodeGen   = enclosing.useCodeGen

    initZ3

    val solver = z3.mkSolver

    for(funDef <- program.definedFunctions) {
      if (funDef.annotations.contains("axiomatize") && !axiomatizedFunctions(funDef)) {
        reporter.warning("Function " + funDef.id + " was marked for axiomatization but could not be handled.")
      }
    }

    private var varsInVC = Set[Identifier]()

    private var frameExpressions = List[List[Expr]](Nil)

    val unrollingBank = new UnrollingBank()

    def push() {
      solver.push()
      unrollingBank.push()
      frameExpressions = Nil :: frameExpressions
    }

    override def init() {
      FairZ3Solver.super.init
    }

    def halt() {
      FairZ3Solver.super.halt
      if(z3 ne null) {
        z3.interrupt
      }
    }

    def pop(lvl: Int = 1) {
      solver.pop(lvl)
      unrollingBank.pop(lvl)
      frameExpressions = frameExpressions.drop(lvl)
    }

    def check: Option[Boolean] = {
      fairCheck(Set())
    }

    def checkAssumptions(assumptions: Set[Expr]): Option[Boolean] = {
      fairCheck(assumptions)
    }

    var foundDefinitiveAnswer = false
    var definitiveAnswer : Option[Boolean] = None
    var definitiveModel  : Map[Identifier,Expr] = Map.empty
    var definitiveCore   : Set[Expr] = Set.empty

    def assertCnstr(expression: Expr) {
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
      val totalTime     = new Stopwatch().start
      val luckyTime     = new Stopwatch()
      val z3Time        = new Stopwatch()
      val scalaTime     = new Stopwatch()
      val unrollingTime = new Stopwatch()
      val unlockingTime = new Stopwatch()

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

      while(!foundDefinitiveAnswer && !forceStop) {

        //val blockingSetAsZ3 : Seq[Z3AST] = blockingSet.toSeq.map(toZ3Formula(_).get)
        // println("Blocking set : " + blockingSet)

        reporter.info(" - Running Z3 search...")

        // reporter.info("Searching in:\n"+solver.getAssertions.toSeq.mkString("\nAND\n"))
        // reporter.info("Unroll.  Assumptions:\n"+unrollingBank.z3CurrentZ3Blockers.mkString("  &&  "))
        // reporter.info("Userland Assumptions:\n"+assumptionsAsZ3.mkString("  &&  "))

        z3Time.start
        solver.push() // FIXME: remove when z3 bug is fixed
        val res = solver.checkAssumptions((assumptionsAsZ3 ++ unrollingBank.z3CurrentZ3Blockers) :_*)
        solver.pop()  // FIXME: remove when z3 bug is fixed
        z3Time.stop

        reporter.info(" - Finished search with blocked literals")

        res match {
          case None =>
            // reporter.warning("Z3 doesn't know because: " + z3.getSearchFailure.message)
            reporter.warning("Z3 doesn't know because ??")
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
              scalaTime.start
              val model = modelToMap(z3model, varsInVC)
              scalaTime.stop

              //lazy val modelAsString = model.toList.map(p => p._1 + " -> " + p._2).mkString("\n")
              //reporter.info("- Found a model:")
              //reporter.info(modelAsString)

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

            //reporter.info("UNSAT BECAUSE: "+solver.getUnsatCore.mkString("\n  AND  \n"))
            //reporter.info("UNSAT BECAUSE: "+core.mkString("  AND  "))

            if (!forceStop) {
              if (this.feelingLucky) {
                // we need the model to perform the additional test
                reporter.info(" - Running search without blocked literals (w/ lucky test)")
              } else {
                reporter.info(" - Running search without blocked literals (w/o lucky test)")
              }

              z3Time.start
              solver.push() // FIXME: remove when z3 bug is fixed
              val res2 = solver.checkAssumptions(assumptionsAsZ3 : _*)
              solver.pop()  // FIXME: remove when z3 bug is fixed
              z3Time.stop

              res2 match {
                case Some(false) =>
                  //reporter.info("UNSAT WITHOUT Blockers")
                  foundAnswer(Some(false), core = z3CoreToCore(solver.getUnsatCore))
                case Some(true) =>
                  //reporter.info("SAT WITHOUT Blockers")
                  if (this.feelingLucky && !forceStop) {
                    // we might have been lucky :D
                    luckyTime.start
                    val (wereWeLucky, cleanModel) = validateModel(solver.getModel, entireFormula, varsInVC, silenceErrors = true)
                    luckyTime.stop

                    if(wereWeLucky) {
                      foundAnswer(Some(true), cleanModel)
                    }
                  }

                case None =>
                  foundAnswer(None)
              }
            }

            if(forceStop) {
              foundAnswer(None)
            }

            if(!foundDefinitiveAnswer) { 
              reporter.info("- We need to keep going.")

              val toRelease = unrollingBank.getZ3BlockersToUnlock

              reporter.info(" - more unrollings")

              for(id <- toRelease) {
                unlockingTime.start
                val newClauses = unrollingBank.unlock(id)
                unlockingTime.stop

                unrollingTime.start
                for(ncl <- newClauses) {
                  solver.assertCnstr(ncl)
                }
                unrollingTime.stop
              }

              reporter.info(" - finished unrolling")
            }
        }
      }

      totalTime.stop
      StopwatchCollections.get("FairZ3 Total")       += totalTime
      StopwatchCollections.get("FairZ3 Lucky Tests") += luckyTime
      StopwatchCollections.get("FairZ3 Z3")          += z3Time
      StopwatchCollections.get("FairZ3 Unrolling")   += unrollingTime
      StopwatchCollections.get("FairZ3 Unlocking")   += unlockingTime
      StopwatchCollections.get("FairZ3 ScalaTime")   += scalaTime

      //reporter.info(" !! DONE !! ")

      if(forceStop) {
        None
      } else {
        definitiveAnswer
      }
    }

    if (program == null) {
      reporter.error("Z3 Solver was not initialized with a PureScala Program.")
      None
    }
  }

}
