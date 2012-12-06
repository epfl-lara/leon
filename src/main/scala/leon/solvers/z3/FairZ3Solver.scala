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

class FairZ3Solver(context : LeonContext) extends Solver(context) with AbstractZ3Solver with Z3ModelReconstruction {
  // have to comment this to use the solver for constraint solving...
  // assert(Settings.useFairInstantiator)

  private val UNKNOWNASSAT : Boolean = !Settings.noForallAxioms

  val description = "Fair Z3 Solver"
  override val shortDescription = "Z3-f"

  // this is fixed
  protected[leon] val z3cfg = new Z3Config(
    "MODEL" -> true,
    "MBQI" -> false,
    // "SOFT_TIMEOUT" -> 100,
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

  private def prepareAxioms(solver: Z3Solver): Unit = {
    assert(!Settings.noForallAxioms)
    program.definedFunctions.foreach(_ match {
      case fd @ Catamorphism(acd, cases) => {
        assert(!fd.hasPrecondition && fd.hasImplementation)
        reporter.info("Will attempt to axiomatize the function definition:")
        reporter.info(fd)
        for(cse <- cases) {
          val (cc @ CaseClass(ccd, args), expr) = cse
          assert(args.forall(_.isInstanceOf[Variable]))
          val argsAsIDs = args.map(_.asInstanceOf[Variable].id)
          assert(variablesOf(expr) -- argsAsIDs.toSet == Set.empty)
          val axiom : Z3AST = if(args.isEmpty) {
            val eq = Equals(FunctionInvocation(fd, Seq(cc)), expr)
            toZ3Formula(eq).get
          } else {
            val z3ArgSorts = argsAsIDs.map(i => typeToSort(i.getType))
            val boundVars = z3ArgSorts.zipWithIndex.map(p => z3.mkBound(p._2, p._1))
            val map : Map[Identifier,Z3AST] = (argsAsIDs zip boundVars).toMap
            val eq = Equals(FunctionInvocation(fd, Seq(cc)), expr)
            val z3IzedEq = toZ3Formula(eq, map).get
            val z3IzedCC = toZ3Formula(cc, map).get
            val pattern = z3.mkPattern(functionDefToDecl(fd)(z3IzedCC))
            val nameTypePairs = z3ArgSorts.map(s => (z3.mkFreshIntSymbol, s))
            z3.mkForAll(0, List(pattern), nameTypePairs, z3IzedEq)
          }
          // println("I'll assert now an axiom: " + axiom)
          // println("Case axiom:")
          // println(axiom)
          solver.assertCnstr(axiom)
        }

        if(fd.hasPostcondition) {
          // we know it doesn't contain any function invocation
          val cleaned = matchToIfThenElse(expandLets(fd.postcondition.get))
          val argSort = typeToSort(fd.args(0).getType)
          val bound = z3.mkBound(0, argSort)
          val subst = replace(Map(ResultVariable() -> FunctionInvocation(fd, Seq(fd.args(0).toVariable))), cleaned)
          val z3IzedPost = toZ3Formula(subst, Map(fd.args(0).id -> bound)).get
          val pattern = z3.mkPattern(functionDefToDecl(fd)(bound))
          val nameTypePairs = Seq((z3.mkFreshIntSymbol, argSort))
          val postAxiom = z3.mkForAll(0, List(pattern), nameTypePairs, z3IzedPost)
          //println("Post axiom:")
          //println(postAxiom)
          solver.assertCnstr(postAxiom)
        }

        axiomatizedFunctions += fd
      }
      case _ => ;
    })
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
    private val blockMap : MutableMap[(Identifier,Boolean),Set[FunctionInvocation]] = MutableMap.empty
    private def registerBlocked(id: Identifier, pol: Boolean, fi: FunctionInvocation) : Boolean = 
      registerBlocked(id,pol,Set(fi))
    private def registerBlocked(id: Identifier, pol: Boolean, fis: Set[FunctionInvocation]) : Boolean = {
      val filtered = fis.filter(i => {
        val FunctionInvocation(fd, _) = i
        !axiomatizedFunctions(fd)
      })

      if(!filtered.isEmpty) {
        val pair = (id, pol)
        val alreadyBlocked = blockMap.get(pair)
        alreadyBlocked match {
          case None => blockMap(pair) = filtered
          case Some(prev) => blockMap(pair) = prev ++ filtered
        }
        true
      } else {
        false
      }
    }

    def scanForNewTemplates(expr: Expr): (Seq[Expr], Seq[(Identifier, Boolean)]) = {
      val tmp = FunctionTemplate.mkTemplate(expr)

      val allBlocks : MutableSet[(Identifier,Boolean)] = MutableSet.empty

      for (((i, p), fis) <- tmp.blockers) {
        if(registerBlocked(i, p, fis)) {
          allBlocks += i -> p
        }
      }

      (tmp.asClauses, allBlocks.toSeq)
    }

    private def treatFunctionInvocationSet(sVar : Identifier, pol : Boolean, fis : Set[FunctionInvocation]) : (Seq[Expr],Seq[(Identifier,Boolean)]) = {
      val allBlocks : MutableSet[(Identifier,Boolean)] = MutableSet.empty
      var allNewExprs : Seq[Expr] = Seq.empty

      for(fi <- fis) {
        val temp = FunctionTemplate.mkTemplate(fi.funDef)
        val (newExprs,newBlocks) = temp.instantiate(sVar, pol, fi.args)

        for(((i, p), fis) <- newBlocks) {
          if(registerBlocked(i, p, fis)) {
            allBlocks += i -> p
          }
        }
        allNewExprs = allNewExprs ++ newExprs
      }
      (allNewExprs, allBlocks.toSeq)
    }

    def unlock(id: Identifier, pol: Boolean) : (Seq[Expr], Seq[(Identifier,Boolean)]) = {
      if(!blockMap.isDefinedAt((id,pol))) {
        (Seq.empty,Seq.empty)
      } else {
        val copy = blockMap((id,pol))
        blockMap((id,pol)) = Set.empty
        treatFunctionInvocationSet(id, pol, copy)
      }
    }
  }

  def getNewSolver = new solvers.IncrementalSolver {

    initZ3

    val solver = z3.mkSolver

    if(!Settings.noForallAxioms) {
      prepareAxioms(solver)
    }

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

    // Unrolling state
    private var blockingSet: Set[Expr] = Set.empty

    def assertCnstr(expression: Expr) {
      val guard = frameGuards.head

      varsInVC ++= variablesOf(expression)

      frameExpressions = (expression :: frameExpressions.head) :: frameExpressions.tail

      val (newClauses, newGuards) = unrollingBank.scanForNewTemplates(expression)
 
      for (cl <- newClauses) {
        solver.assertCnstr(z3.mkImplies(guard, toZ3Formula(cl).get))
      }

      blockingSet ++= newGuards.map(p => if(p._2) Not(Variable(p._1)) else Variable(p._1))
    }

    def getModel = {
      definitiveModel
    }

    def getUnsatCore = {
      definitiveCore
    }

    def fairCheck(assumptions: Set[Expr]): Option[Boolean] = {
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

      var iterationsLeft : Int = if(Settings.unrollingLevel > 0) Settings.unrollingLevel else 16121984

      while(!foundDefinitiveAnswer && !forceStop) {
        iterationsLeft -= 1

        val blockingSetAsZ3 : Seq[Z3AST] = blockingSet.toSeq.map(toZ3Formula(_).get)
        // println("Blocking set : " + blockingSet)

        reporter.info(" - Running Z3 search...")

        //reporter.info("Searching in:\n"+solver.getAssertions.toSeq.mkString("\nAND\n"))
        //reporter.info("Assumptions:\n"+(blockingSetAsZ3 ++ assumptionsAsZ3).mkString("  AND  "))

        val res = solver.checkAssumptions((blockingSetAsZ3 ++ assumptionsAsZ3) :_*)

        reporter.info(" - Finished search with blocked literals")

        res match {
          case None =>
            // reporter.warning("Z3 doesn't know because: " + z3.getSearchFailure.message)
            reporter.warning("Z3 doesn't know because ??")
            foundAnswer(None)

          case Some(true) => // SAT

            val z3model = solver.getModel

            if (Settings.verifyModel && false) {
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

          case Some(false) if blockingSet.isEmpty =>
            val core = z3CoreToCore(solver.getUnsatCore)  

            foundAnswer(Some(false), core = core)

          // This branch is both for with and without unsat cores. The
          // distinction is made inside.
          case Some(false) =>

            val core = z3CoreToCore(solver.getUnsatCore)  

            reporter.info("UNSAT BECAUSE: "+core.mkString(" AND "))

            if (!forceStop) {
              if (Settings.luckyTest && false) {
                // we need the model to perform the additional test
                reporter.info(" - Running search without blocked literals (w/ lucky test)")
              } else {
                reporter.info(" - Running search without blocked literals (w/o lucky test)")
              }

              val res2 = solver.checkAssumptions(assumptionsAsZ3 : _*)

              res2 match {
                case Some(false) =>
                  //reporter.info("UNSAT WITHOUT Blockers")
                  foundAnswer(Some(false), core = z3CoreToCore(solver.getUnsatCore))
                case Some(true) =>
                  //reporter.info("SAT WITHOUT Blockers")
                  if (Settings.luckyTest && !forceStop) {
                    // we might have been lucky :D
                    val (wereWeLucky, cleanModel) = validateAndDeleteModel(solver.getModel, entireFormula, varsInVC)
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

              val toRelease : Set[Expr] = blockingSet

              // reporter.info(" - toRelease   : " + toRelease)
              // reporter.info(" - blockingSet : " + blockingSet)

              var fixedForEver : Set[Expr] = Set.empty

              if(Settings.pruneBranches) {
                for(ex <- blockingSet) ex match {
                  case Not(Variable(b)) =>
                    solver.push
                    solver.assertCnstr(toZ3Formula(Variable(b)).get)
                    solver.check match {
                      case Some(false) =>
                        //println("We had ~" + b + " in the blocking set. We now know it should stay there forever.")
                        solver.pop(1)
                        solver.assertCnstr(toZ3Formula(Not(Variable(b))).get)
                        fixedForEver = fixedForEver + ex

                      case _ =>
                        solver.pop(1)
                    }

                  case Variable(b) =>
                    solver.push
                    solver.assertCnstr(toZ3Formula(Not(Variable(b))).get)
                    solver.check match {
                      case Some(false) =>
                        //println("We had " + b + " in the blocking set. We now know it should stay there forever.")
                        solver.pop(1)
                        solver.assertCnstr(toZ3Formula(Variable(b)).get)
                        fixedForEver = fixedForEver + ex

                      case _ =>
                        solver.pop(1)
                    }

                  case _ =>
                    scala.sys.error("Should not have happened.")
                }

                if(fixedForEver.size > 0) {
                  reporter.info("- Pruned out " + fixedForEver.size + " branches.")
                }
              }

              blockingSet = blockingSet -- toRelease

              val toReleaseAsPairs : Set[(Identifier,Boolean)] = (toRelease -- fixedForEver).map(b => b match {
                case Variable(id) => (id, true)
                case Not(Variable(id)) => (id, false)
                case _ => scala.sys.error("Impossible value in release set: " + b)
              })

              reporter.info(" - more unrollings")
              for((id,polarity) <- toReleaseAsPairs) {
                val (newClauses,newBlockers) = unrollingBank.unlock(id, !polarity)

                for(ncl <- newClauses) {
                  solver.assertCnstr(toZ3Formula(ncl).get)
                }
                blockingSet = blockingSet ++ Set(newBlockers.map(p => if(p._2) Not(Variable(p._1)) else Variable(p._1)) : _*)
              }
              reporter.info(" - finished unrolling")
            }
        }

        if(iterationsLeft <= 0) {
          reporter.error(" - Max. number of iterations reached.")
          foundAnswer(None)
        }
      }

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

