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
    LeonFlagOptionDef("checkmodels",  "--checkmodels",  "Double-check counter-examples"),
    LeonFlagOptionDef("feelinglucky", "--feelinglucky", "Use evaluator to find counter-examples early")
  )

  val (feelingLucky, checkModels) = locally {
    var lucky = false
    var check = false

    for(opt <- context.options) opt match {
      case LeonFlagOption("checkmodels") => check = true
      case LeonFlagOption("feelinglucky") => lucky = true
      case _ =>
    }

    (lucky,check)
  }

  // this is fixed
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

  def prepareFunctions: Unit = {
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
      z3.softCheckCancel
    }
  }

  override def solveSATWithCores(expression: Expr, assumptions: Set[Expr]): (Option[Boolean], Map[Identifier, Expr], Set[Expr]) = {
    val solver = getNewSolver
    solver.assertCnstr(expression)
    (solver.checkAssumptions(assumptions), solver.getModel, solver.getUnsatCore)
  }

  private def validateAndDeleteModel(model: Z3Model, formula: Expr, variables: Set[Identifier], evaluator: Option[(Map[Identifier,Expr])=>Boolean] = None) : (Boolean, Map[Identifier,Expr]) = {
    import Evaluator._

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
      val evalResult = eval(asMap, formula, evaluator)

      evalResult match {
        case OK(BooleanLiteral(true)) => {
          reporter.info("- Model validated:")
          reporter.info(modelAsString)
          (true, asMap)
        }
        case RuntimeError(msg) => {
          reporter.info("- Invalid model")
          //reporter.error(modelAsString)
          (false, asMap)
        }
        case OK(BooleanLiteral(false)) => {
          reporter.info("- Invalid model.")
          (false, asMap)
        }
        case ImpossibleComputation() => {
          reporter.info("- Invalid Model: the model could not be verified because of insufficient information.")
          (false, asMap)
        }
        case other => {
          reporter.error("Something went wrong. While evaluating the model, we got this: " + other)
          (false, asMap)
        }
      }
    } else {
      (false, Map.empty)
    }
  }

  class UnrollingBank {
    // Keep which function invocation is guarded by which guard with polarity,
    // also specify the generation of the blocker
    private val blockersInfo : MutableMap[(Identifier,Boolean), (Int, Z3AST, Set[FunctionInvocation])] = MutableMap.empty

    def currentZ3Blockers = blockersInfo.map(_._2._2)

    def canUnroll = !blockersInfo.isEmpty

    def getBlockersToUnlock: Seq[(Identifier, Boolean)] = {
      val minGeneration = blockersInfo.values.map(_._1).min

      blockersInfo.filter(_._2._1 == minGeneration).toSeq.map(_._1)
    }

    private def registerBlocker(gen: Int, id: Identifier, pol: Boolean, fis: Set[FunctionInvocation]) {
      val pair = (id, pol)

      val z3ast          = toZ3Formula(if (pol) Not(Variable(id)) else Variable(id)).get

      blockersInfo.get(pair) match {
        case Some((exGen, _, exFis)) =>
          assert(exGen == gen, "Mixing the same pair "+pair+" with various generations "+ exGen+" and "+gen)

          blockersInfo(pair) = ((gen, z3ast, fis++exFis))
        case None =>
          blockersInfo(pair) = ((gen, z3ast, fis))
      }
    }

    def scanForNewTemplates(expr: Expr): Seq[Expr] = {
      val tmp = FunctionTemplate.mkTemplate(expr)

      for (((i, p), fis) <- tmp.blockers) {
        registerBlocker(0, i, p, fis)
      }

      tmp.asClauses
    }

    def unlock(id: Identifier, pol: Boolean) : Seq[Expr] = {
      val pair = (id, pol)
      assert(blockersInfo contains pair)

      val (gen, _, fis) = blockersInfo(pair)
      blockersInfo -= pair

      var newClauses : Seq[Expr] = Seq.empty

      for(fi <- fis) {
        val temp                  = FunctionTemplate.mkTemplate(fi.funDef)
        val (newExprs, newBlocks) = temp.instantiate(id, pol, fi.args)

        for(((i, p), fis) <- newBlocks) {
          registerBlocker(gen+1, i, p, fis)
        }

        newClauses ++= newExprs
      }

      newClauses
    }
  }

  def getNewSolver = new solvers.IncrementalSolver {
    private val feelingLucky = enclosing.feelingLucky
    private val checkModels  = enclosing.checkModels

    initZ3

    val solver = z3.mkSolver

    for(funDef <- program.definedFunctions) {
      if (funDef.annotations.contains("axiomatize") && !axiomatizedFunctions(funDef)) {
        reporter.warning("Function " + funDef.id + " was marked for axiomatization but could not be handled.")
      }
    }

    private var frameGuards      = List[Z3AST](z3.mkFreshConst("frame", z3.mkBoolSort))
    private var frameExpressions = List[List[Expr]](Nil)
    private var varsInVC         = Set[Identifier]()

    def entireFormula  = And(frameExpressions.flatten)

    def push() {
      frameGuards      = z3.mkFreshConst("frame", z3.mkBoolSort) :: frameGuards
      frameExpressions = Nil :: frameExpressions
    }

    def pop(lvl: Int = 1) {
      // We make sure we discard the expressions guarded by this frame
      solver.assertCnstr(z3.mkNot(frameGuards.head))

      // Pop the frames
      frameGuards      = frameGuards.tail
      frameExpressions = frameExpressions.tail
    }

    def check: Option[Boolean] = {
      fairCheck(Set())
    }

    def checkAssumptions(assumptions: Set[Expr]): Option[Boolean] = {
      fairCheck(assumptions)
    }

    val unrollingBank = new UnrollingBank()

    var foundDefinitiveAnswer = false
    var definitiveAnswer : Option[Boolean] = None
    var definitiveModel  : Map[Identifier,Expr] = Map.empty
    var definitiveCore   : Set[Expr] = Set.empty

    def assertCnstr(expression: Expr) {
      val guard = frameGuards.head

      varsInVC ++= variablesOf(expression)

      frameExpressions = (expression :: frameExpressions.head) :: frameExpressions.tail

      val newClauses = unrollingBank.scanForNewTemplates(expression)

      for (cl <- newClauses) {
        solver.assertCnstr(z3.mkImplies(guard, toZ3Formula(cl).get))
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
      val unrollingTime = new Stopwatch()

      foundDefinitiveAnswer = false

      def foundAnswer(answer : Option[Boolean], model : Map[Identifier,Expr] = Map.empty, core: Set[Expr] = Set.empty) : Unit = {
        foundDefinitiveAnswer = true
        definitiveAnswer = answer
        definitiveModel  = model
        definitiveCore   = core
      }

      def z3CoreToCore(core: Seq[Z3AST]): Set[Expr] = {
        val internalAssumptions = frameGuards.toSet
        val userlandAssumptions = core.filterNot(internalAssumptions)

        userlandAssumptions.map(ast => fromZ3Formula(null, ast, None) match {
            case n @ Not(Variable(_)) => n
            case v @ Variable(_) => v
            case x => scala.sys.error("Impossible element extracted from core: " + ast + " (as Leon tree : " + x + ")")
        }).toSet
      }

      // these are the optional sequence of assumption literals
      val assumptionsAsZ3: Seq[Z3AST] = frameGuards ++ assumptions.map(toZ3Formula(_).get)

      while(!foundDefinitiveAnswer && !forceStop) {

        //val blockingSetAsZ3 : Seq[Z3AST] = blockingSet.toSeq.map(toZ3Formula(_).get)
        // println("Blocking set : " + blockingSet)

        reporter.info(" - Running Z3 search...")

        //reporter.info("Searching in:\n"+solver.getAssertions.toSeq.mkString("\nAND\n"))
        //reporter.info("UAssumptions:\n"+unrollingBank.currentZ3Blockers.mkString("  &&  "))
        //reporter.info("Assumptions:\n"+(unrollingBank.currentZ3Blockers ++ assumptionsAsZ3).mkString("  AND  "))

        z3Time.start
        val res = solver.checkAssumptions((assumptionsAsZ3 ++ unrollingBank.currentZ3Blockers) :_*)
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
              val (isValid, model) = validateAndDeleteModel(z3model, entireFormula, varsInVC)

              if (isValid) {
                foundAnswer(Some(true), model)
              } else {
                reporter.error("Something went wrong. The model should have been valid, yet we got this : ")
                reporter.error(model)
                foundAnswer(None, model)
              }
            } else {
              val model = modelToMap(z3model, varsInVC)

              lazy val modelAsString = model.toList.map(p => p._1 + " -> " + p._2).mkString("\n")
              reporter.info("- Found a model:")
              reporter.info(modelAsString)

              foundAnswer(Some(true), model)
            }

          case Some(false) if !unrollingBank.canUnroll =>
            val core = z3CoreToCore(solver.getUnsatCore)

            foundAnswer(Some(false), core = core)

          // This branch is both for with and without unsat cores. The
          // distinction is made inside.
          case Some(false) =>

            val core = z3CoreToCore(solver.getUnsatCore)

            reporter.info("UNSAT BECAUSE: "+core.mkString(" AND "))

            if (!forceStop) {
              if (this.feelingLucky) {
                // we need the model to perform the additional test
                reporter.info(" - Running search without blocked literals (w/ lucky test)")
              } else {
                reporter.info(" - Running search without blocked literals (w/o lucky test)")
              }

              z3Time.start
              val res2 = solver.checkAssumptions(assumptionsAsZ3 : _*)
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
                    val (wereWeLucky, cleanModel) = validateAndDeleteModel(solver.getModel, entireFormula, varsInVC)
                    luckyTime.stop

                    if(wereWeLucky) {
                      foundAnswer(Some(true), cleanModel)
                    }
                  }
                case None =>
              }
            }

            if(forceStop) {
              foundAnswer(None)
            }

            if(!foundDefinitiveAnswer) { 
              reporter.info("- We need to keep going.")

              val toReleaseAsPairs = unrollingBank.getBlockersToUnlock

              reporter.info(" - more unrollings")

              for((id, polarity) <- toReleaseAsPairs) {
                unrollingTime.start
                val newClauses = unrollingBank.unlock(id, polarity)
                unrollingTime.stop

                for(ncl <- newClauses) {
                  solver.assertCnstr(toZ3Formula(ncl).get)
                }
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
