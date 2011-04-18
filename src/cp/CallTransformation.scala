package cp

import scala.tools.nsc.transform.TypingTransformers
import scala.tools.nsc.ast.TreeDSL
import purescala.FairZ3Solver
import purescala.{DefaultReporter,QuietReporter}
import purescala.Common.Identifier
import purescala.Definitions._
import purescala.Trees._

trait CallTransformation 
  extends TypingTransformers
  with CodeGeneration
  with TreeDSL
{
  self: CPComponent =>
  import global._
  import CODE._

  private lazy val cpPackage = definitions.getModule("cp")
  private lazy val cpDefinitionsModule = definitions.getModule("cp.Definitions")

  val purescalaReporter = purescala.Settings.reporter

  /** Collect all choose and findAll signatures in program */
  def chooseSignatures(unit: CompilationUnit) : Set[List[Tree]] = {
    val signatures : scala.collection.mutable.Set[List[Tree]] = scala.collection.mutable.Set[List[Tree]]()
    def collectSignatures(tree: Tree) = tree match {
      case Apply(TypeApply(Select(s: Select, n), typeTreeList), List(predicate: Function)) if (cpDefinitionsModule == s.symbol && 
          (n.toString == "choose" || n.toString == "find" || n.toString == "findAll")) =>
        signatures += typeTreeList
      case _ => 
    }
    new ForeachTreeTraverser(collectSignatures).traverse(unit.body)

    signatures.toSet
  }

  def predicateMap(unit: CompilationUnit) : Map[Position,(FunDef,Option[Expr],Option[Expr])] = {
    val extracted = scala.collection.mutable.Map[Position,(FunDef,Option[Expr],Option[Expr])]()
    def extractPredicates(tree: Tree) = tree match {
      case Apply(TypeApply(Select(s: Select, n), typeTreeList), List(predicate: Function)) if (cpDefinitionsModule == s.symbol && 
          (n.toString == "choose" || n.toString == "find" || n.toString == "findAll")) =>
        val Function(funValDefs, funBody) = predicate
        extracted += (predicate.pos -> extractPredicate(unit, funValDefs, funBody))
      case _ => 
    }
    new ForeachTreeTraverser(extractPredicates).traverse(unit.body)

    extracted.toMap
  }

  def transformCalls(unit: CompilationUnit, prog: Program, progString : String, progId : Int) : Unit =
    unit.body = new CallTransformer(unit, prog, progString, progId).transform(unit.body)
  
  class CallTransformer(unit: CompilationUnit, prog: Program, progString: String, progId : Int) extends TypingTransformer(unit) {
    var exprToScalaSym : Symbol = null
    var exprToScalaCastSym : Symbol = null
    var scalaToExprSym : Symbol = null
    val exprSeqToScalaSyms : scala.collection.mutable.Map[List[Tree],Symbol] = scala.collection.mutable.Map[List[Tree],Symbol]()

    val extractedPredicates : Map[Position,(FunDef,Option[Expr],Option[Expr])] = predicateMap(unit)

    override def transform(tree: Tree) : Tree = {
      tree match {
        case a @ Apply(TypeApply(Select(s: Select, n), typeTreeList), rhs @ List(predicate: Function)) if (cpDefinitionsModule == s.symbol && n.toString == "choose") => {
          val Function(funValDefs, funBody) = predicate

          val (fd, minExpr, maxExpr) = extractedPredicates(predicate.pos)
          val outputVars : Seq[Identifier] = fd.args.map(_.id)

          purescalaReporter.info("Considering predicate:") 
          purescalaReporter.info(fd)

          val codeGen = new CodeGenerator(unit, currentOwner, tree.pos)

          fd.body match {
            case None => purescalaReporter.error("Could not extract `choose' predicate: " + funBody); super.transform(tree)
            case Some(b) =>
              // serialize expression
              val (exprString, exprId) = serialize(b)
              
              // compute input variables
              val inputVars : Seq[Identifier] = (variablesOf(b) ++ (minExpr match {
                case Some(e) => variablesOf(e)
                case None => Set.empty
              }) ++ (maxExpr match {
                case Some(e) => variablesOf(e)
                case None => Set.empty
              })).filter(!outputVars.contains(_)).toSeq

              purescalaReporter.info("Input variables  : " + inputVars.mkString(", "))
              purescalaReporter.info("Output variables : " + outputVars.mkString(", "))

              // serialize list of input "Variable"s
              val (inputVarListString, inputVarListId) = serialize(inputVars map (iv => Variable(iv)))

              // serialize outputVars sequence
              val (outputVarsString, outputVarsId) = serialize(outputVars)

              // input constraints
              val inputConstraints : Seq[Tree] = (for (iv <- inputVars) yield {
                codeGen.inputEquality(inputVarListString, inputVarListId, iv, scalaToExprSym)
              })

              val inputConstraintsConjunction = if (inputVars.isEmpty) codeGen.trueLiteral else codeGen.andExpr(inputConstraints)

              val exprSeqTree = (minExpr, maxExpr) match {
                case (None, None) => {
                  codeGen.chooseExecCode(progString, progId, exprString, exprId, outputVarsString, outputVarsId, inputConstraintsConjunction)
                }
                case (Some(minE), None) => {
                  val (minExprString, minExprId) = serialize(minE)
                  codeGen.chooseMinimizingExecCode(progString, progId, exprString, exprId, outputVarsString, outputVarsId, minExprString, minExprId, inputConstraintsConjunction)
                }
                case (None, Some(maxE)) => {
                  val (maxExprString, maxExprId) = serialize(maxE)
                  codeGen.chooseMaximizingExecCode(progString, progId, exprString, exprId, outputVarsString, outputVarsId, maxExprString, maxExprId, inputConstraintsConjunction)
                }
                case _ =>
                  scala.Predef.error("Unreachable case")
              }

              typer.typed(atOwner(currentOwner) {
                exprSeqToScalaSyms(typeTreeList) APPLY exprSeqTree
              })
          }
        }

        case a @ Apply(TypeApply(Select(s: Select, n), typeTreeList), rhs @ List(predicate: Function)) if (cpDefinitionsModule == s.symbol && n.toString == "find") => {
          val Function(funValDefs, funBody) = predicate

          val (fd, minExpr, maxExpr) = extractedPredicates(predicate.pos)
          val outputVars : Seq[Identifier] = fd.args.map(_.id)

          purescalaReporter.info("Considering predicate:") 
          purescalaReporter.info(fd)

          val codeGen = new CodeGenerator(unit, currentOwner, tree.pos)

          fd.body match {
            case None => purescalaReporter.error("Could not extract `find' predicate: " + funBody); super.transform(tree)
            case Some(b) =>
              // serialize expression
              val (exprString, exprId) = serialize(b)
              
              // compute input variables
              val inputVars : Seq[Identifier] = (variablesOf(b) ++ (minExpr match {
                case Some(e) => variablesOf(e)
                case None => Set.empty
              }) ++ (maxExpr match {
                case Some(e) => variablesOf(e)
                case None => Set.empty
              })).filter(!outputVars.contains(_)).toSeq


              purescalaReporter.info("Input variables  : " + inputVars.mkString(", "))
              purescalaReporter.info("Output variables : " + outputVars.mkString(", "))

              // serialize list of input "Variable"s
              val (inputVarListString, inputVarListId) = serialize(inputVars map (iv => Variable(iv)))

              // serialize outputVars sequence
              val (outputVarsString, outputVarsId) = serialize(outputVars)

              // input constraints
              val inputConstraints : Seq[Tree] = (for (iv <- inputVars) yield {
                codeGen.inputEquality(inputVarListString, inputVarListId, iv, scalaToExprSym)
              })

              val inputConstraintsConjunction = if (inputVars.isEmpty) codeGen.trueLiteral else codeGen.andExpr(inputConstraints)

              val exprSeqOptionTree = (minExpr, maxExpr) match {
                case (None, None) => {
                  codeGen.findExecCode(progString, progId, exprString, exprId, outputVarsString, outputVarsId, inputConstraintsConjunction)
                }
                case (Some(minE), None) => {
                  val (minExprString, minExprId) = serialize(minE)
                  codeGen.findMinimizingExecCode(progString, progId, exprString, exprId, outputVarsString, outputVarsId, minExprString, minExprId, inputConstraintsConjunction)
                }
                case (None, Some(maxE)) => {
                  val (maxExprString, maxExprId) = serialize(maxE)
                  codeGen.findMaximizingExecCode(progString, progId, exprString, exprId, outputVarsString, outputVarsId, maxExprString, maxExprId, inputConstraintsConjunction)
                }
                case _ =>
                  scala.Predef.error("Unreachable case")
              }

              typer.typed(atOwner(currentOwner) {
                codeGen.mapOption(exprSeqToScalaSyms(typeTreeList), exprSeqOptionTree)
              })
          }
        }

        case a @ Apply(TypeApply(Select(s: Select, n), typeTreeList), rhs @ List(predicate: Function)) if (cpDefinitionsModule == s.symbol && n.toString == "findAll") => {
          val Function(funValDefs, funBody) = predicate

          val (fd, minExpr, maxExpr) = extractedPredicates(predicate.pos)
          val outputVars : Seq[Identifier] = fd.args.map(_.id)

          purescalaReporter.info("Considering predicate:") 
          purescalaReporter.info(fd)

          val codeGen = new CodeGenerator(unit, currentOwner, tree.pos)

          fd.body match {
            case None => purescalaReporter.error("Could not extract choose predicate: " + funBody); super.transform(tree)
            case Some(b) =>
              // serialize expression
              val (exprString, exprId) = serialize(b)
              
              // compute input variables
              val inputVars : Seq[Identifier] = (variablesOf(b) ++ (minExpr match {
                case Some(e) => variablesOf(e)
                case None => Set.empty
              }) ++ (maxExpr match {
                case Some(e) => variablesOf(e)
                case None => Set.empty
              })).filter(!outputVars.contains(_)).toSeq

              purescalaReporter.info("Input variables  : " + inputVars.mkString(", "))
              purescalaReporter.info("Output variables : " + outputVars.mkString(", "))

              // serialize list of input "Variable"s
              val (inputVarListString, inputVarListId) = serialize(inputVars map (iv => Variable(iv)))

              // serialize outputVars sequence
              val (outputVarsString, outputVarsId) = serialize(outputVars)

              // input constraints
              val inputConstraints : Seq[Tree] = (for (iv <- inputVars) yield {
                codeGen.inputEquality(inputVarListString, inputVarListId, iv, scalaToExprSym)
              })

              val inputConstraintsConjunction = if (inputVars.isEmpty) codeGen.trueLiteral else codeGen.andExpr(inputConstraints)

              val exprSeqIteratorTree = (minExpr, maxExpr) match {
                case (None, None) =>
                  codeGen.findAllExecCode(progString, progId, exprString, exprId, outputVarsString, outputVarsId, inputConstraintsConjunction)
                case (Some(minE), None) =>
                  val (minExprString, minExprId) = serialize(minE)
                  codeGen.findAllMinimizingExecCode(progString, progId, exprString, exprId, outputVarsString, outputVarsId, minExprString, minExprId, inputConstraintsConjunction)
                case (None, Some(maxE)) =>
                  throw new Exception("not implemented")
                case _ => 
                  scala.Predef.error("This case should be unreachable")
              }

              val code = codeGen.mapIterator(exprSeqToScalaSyms(typeTreeList), exprSeqIteratorTree)

              typer.typed(atOwner(currentOwner) {
                code
              })
          }
        }

        // Insert generated method definitions
        case cd @ ClassDef(mods, name, tparams, impl) if (cd.symbol.isModuleClass && tparams.isEmpty && !cd.symbol.isSynthetic) => {
          val codeGen = new CodeGenerator(unit, currentOwner, tree.pos)

          val ((e2sSym, exprToScalaCode), (e2sCastSym,exprToScalaCastCode)) = codeGen.exprToScalaMethods(cd.symbol, prog)
          exprToScalaSym      = e2sSym
          exprToScalaCastSym  = e2sCastSym

          val (scalaToExprCode, s2eSym)                                     = codeGen.scalaToExprMethod(cd.symbol, prog, progString, progId)
          scalaToExprSym      = s2eSym

          val skipCounter                                                   = codeGen.skipCounter(purescala.Common.FreshIdentifier.last)

          val exprSeqToScalaCodes : List[Tree] = (for (sig <- chooseSignatures(unit)) yield {
            val (exprSeqToScalaCode, exprSeqToScalaSym) = codeGen.exprSeqToScalaMethod(cd.symbol, exprToScalaCastSym, sig)
            exprSeqToScalaSyms += (sig -> exprSeqToScalaSym)
            exprSeqToScalaCode
          }).toList

          atOwner(tree.symbol) {
            treeCopy.ClassDef(tree, transformModifiers(mods), name,
                              transformTypeDefs(tparams), impl match {
                                case Template(parents, self, body) =>
                                  treeCopy.Template(impl, transformTrees(parents),
                                    transformValDef(self), 
                                      typer.typed(atOwner(currentOwner) {exprToScalaCode}) ::
                                      typer.typed(atOwner(currentOwner) {exprToScalaCastCode}) :: 
                                      typer.typed(atOwner(currentOwner) {scalaToExprCode}) :: 
                                      typer.typed(atOwner(currentOwner) {skipCounter}) ::
                                      exprSeqToScalaCodes.map(es2sc => typer.typed(atOwner(currentOwner) {es2sc})) :::
                                      transformStats(body, tree.symbol))
                              }) 
          }
        }

        case _ => super.transform(tree)
      }
    }
  }
}

/** A collection of methods that are called on runtime */
object CallTransformation {
  import Serialization._
  import Definitions.UnsatisfiableConstraintException
  import Definitions.UnknownConstraintException

  private def newReporter() = new QuietReporter()
  // private def newReporter() = new DefaultReporter()
  private def newSolver() = new FairZ3Solver(newReporter())

  def chooseExec(progString : String, progId : Int, exprString : String, exprId : Int, outputVarsString : String, outputVarsId : Int, inputConstraints : Expr) : Seq[Expr] = {
    val program    = deserialize[Program](progString, progId)
    val expr       = deserialize[Expr](exprString, exprId)
    val outputVars = deserialize[Seq[Identifier]](outputVarsString, outputVarsId)

    chooseExec(program, expr, outputVars, inputConstraints)
  }

  private def chooseExec(program : Program, expr : Expr, outputVars : Seq[Identifier], inputConstraints : Expr) : Seq[Expr] = {
    val solver = newSolver()
    solver.setProgram(program)

    val toCheck = expr :: inputConstraints :: Nil
    val (outcome, model) = solver.restartAndDecideWithModel(And(toCheck), false)

    outcome match {
      case Some(false) =>
        outputVars.map(v => modelValue(v, model))
      case Some(true) =>
        throw new UnsatisfiableConstraintException()
      case None =>
        throw new UnknownConstraintException()
    }
  }

  def chooseMinimizingExec(progString : String, progId : Int, exprString : String, exprId : Int, outputVarsString : String, outputVarsId : Int, minExprString : String, minExprId : Int, inputConstraints : Expr) : Seq[Expr] = {
    val program    = deserialize[Program](progString, progId)
    val expr       = deserialize[Expr](exprString, exprId)
    val outputVars = deserialize[Seq[Identifier]](outputVarsString, outputVarsId)
    val minExpr    = deserialize[Expr](minExprString, minExprId)

    chooseMinimizingExec(program, expr, outputVars, minExpr, inputConstraints)
  }

  private def chooseMinimizingExec(program : Program, expr : Expr, outputVars : Seq[Identifier], minExpr : Expr, inputConstraints : Expr) : Seq[Expr] = {
    chooseMinimizingModelAndValue(program, expr, outputVars, minExpr, inputConstraints)._1
  }

  private def chooseMinimizingModelAndValue(program : Program, expr : Expr, outputVars : Seq[Identifier], minExpr : Expr, inputConstraints : Expr) : (Seq[Expr], Int) = {
    def stop(lo : Option[Int], hi : Int) : Boolean = lo match {
      case Some(l) => hi - l <= 2
      case None => false
    }
    
    val solver = newSolver()
    solver.setProgram(program)

    /* invariant : lo is always stricly less than any sat. minExpr assignment,
     * and there is always a sat. assignment less than hi */
    def minAux(pivot : Int, lo : Option[Int], hi : Int) : (Map[Identifier, Expr], Int) = {
      // println("Iterating:")
      // println("  lo     : " + (lo match { case Some(l) => l; case None => "-inf"}))
      // println("  pivot  : " + pivot)
      // println("  hi     : " + hi)
      // println
      val toCheck = expr :: inputConstraints :: LessEquals(minExpr, IntLiteral(pivot)) :: Nil
      val (outcome, model) = solver.restartAndDecideWithModel(And(toCheck), false)

      outcome match {
        case Some(false) =>
          // there is a satisfying assignment
          if (stop(lo, hi)) {
            (model, pivot)
          } else {
            lo match {
              case None =>
                // lower bound is -inf
                minAux(
                  if (pivot >= 0) -1 else pivot * 2,
                  None,
                  pivot + 1
                )
              case Some(lv) =>
                minAux(
                  lv + (pivot + 1 - lv) / 2,
                  lo,
                  pivot + 1
                )
            }
          }
        case _ =>
          // new lo is pivot
          minAux(
            pivot + (hi - pivot) / 2,
            Some(pivot),
            hi
          )
      }
    }

    // We declare a variable to hold the value to minimize:
    val minExprID = purescala.Common.FreshIdentifier("minExpr").setType(purescala.TypeTrees.Int32Type)

    solver.restartAndDecideWithModel(And(expr :: inputConstraints :: Equals(minExpr, Variable(minExprID)) :: Nil), false) match {
      case (Some(false), model) =>
        // there is a satisfying assignment
        val minExprVal = modelValue(minExprID, model) match {
          case IntLiteral(i) => i
          case e => scala.Predef.error("Unexpected value for term to minimize : " + e)
        }

        val (optimalModel, optimalValue) = minAux(minExprVal - 1, None, minExprVal + 1)
        (outputVars.map(v => modelValue(v, optimalModel)), optimalValue)
      case (Some(true), _) =>
        throw new UnsatisfiableConstraintException()
      case _ =>
        throw new UnknownConstraintException()
    }
  }

  def chooseMaximizingExec(progString : String, progId : Int, exprString : String, exprId : Int, outputVarsString : String, outputVarsId : Int, maxExprString : String, maxExprId : Int, inputConstraints : Expr) : Seq[Expr] = {
    val program    = deserialize[Program](progString, progId)
    val expr       = deserialize[Expr](exprString, exprId)
    val outputVars = deserialize[Seq[Identifier]](outputVarsString, outputVarsId)
    val maxExpr    = deserialize[Expr](maxExprString, maxExprId)

    chooseMaximizingExec(program, expr, outputVars, maxExpr, inputConstraints)
  }
   
  private def chooseMaximizingExec(program : Program, expr : Expr, outputVars : Seq[Identifier], maxExpr : Expr, inputConstraints : Expr) : Seq[Expr] = {
    def stop(lo : Int, hi : Option[Int]) : Boolean = hi match {
      case Some(h) => h - lo <= 2
      case None => false
    }

    val solver = newSolver()
    solver.setProgram(program)

    /* invariant : hi is always strictly greater than any sat. maxExpr assignment,
     * and there is always a sat. assignment >= lo */
    def maxAux(pivot : Int, lo : Int, hi : Option[Int]) : Map[Identifier, Expr] = {
      // println("Iterating:")
      // println("  lo     : " + lo)
      // println("  pivot  : " + pivot)
      // println("  hi     : " + (hi match { case Some(h) => h; case None => "+inf"}))
      // println
      val toCheck = expr :: inputConstraints :: GreaterEquals(maxExpr, IntLiteral(pivot)) :: Nil
      val (outcome, model) = solver.restartAndDecideWithModel(And(toCheck), false)

      outcome match {
        case Some(false) =>
          // there is a satisfying assignment
          if (stop(lo, hi)) {
            model
          } else {
            hi match {
              case None =>
                // upper bound is +inf
                maxAux(
                  if (pivot <= 0) 1 else pivot * 2,
                  pivot,
                  None
                )
              case Some(hv) =>
                maxAux(
                  pivot + (hv - pivot) / 2,
                  pivot,
                  hi
                )
            }
          }
        case _ =>
          // new hi is pivot
          maxAux(
            lo + (pivot - lo) / 2,
            lo,
            Some(pivot)
          )
      }
    }

    val maxExprID = purescala.Common.FreshIdentifier("maxExpr").setType(purescala.TypeTrees.Int32Type)

    solver.restartAndDecideWithModel(And(expr :: inputConstraints :: Equals(maxExpr, Variable(maxExprID)) :: Nil), false) match {
      case (Some(false), model) =>
        // there is a satisfying assignment
        val maxExprVal = modelValue(maxExprID, model) match {
          case IntLiteral(i) => i
          case e => scala.Predef.error("Unexpected value for term to maximize : " + e)
        }

        val optimalModel = maxAux(maxExprVal, maxExprVal - 1, None)
        outputVars.map(v => modelValue(v, optimalModel))
      case (Some(true),_) =>
        throw new UnsatisfiableConstraintException()
      case _ =>
        throw new UnknownConstraintException()
    }

  }

  def findExec(progString : String, progId : Int, exprString : String, exprId : Int, outputVarsString : String, outputVarsId : Int, inputConstraints : Expr) : Option[Seq[Expr]] = {
    try {
      Some(chooseExec(progString, progId, exprString, exprId, outputVarsString, outputVarsId, inputConstraints))
    } catch {
      case e: UnsatisfiableConstraintException  => None
      case e: UnknownConstraintException        => None
    }
  }

  def findMinimizingExec(progString : String, progId : Int, exprString : String, exprId : Int, outputVarsString : String, outputVarsId : Int, minExprString : String, minExprId : Int, inputConstraints : Expr) : Option[Seq[Expr]] = {
    try {
      Some(chooseMinimizingExec(progString, progId, exprString, exprId, outputVarsString, outputVarsId, minExprString, minExprId, inputConstraints))
    } catch {
      case e: UnsatisfiableConstraintException  => None
      case e: UnknownConstraintException        => None
    }
  }

  def findMaximizingExec(progString : String, progId : Int, exprString : String, exprId : Int, outputVarsString : String, outputVarsId : Int, maxExprString : String, maxExprId : Int, inputConstraints : Expr) : Option[Seq[Expr]] = {
    try {
      Some(chooseMaximizingExec(progString, progId, exprString, exprId, outputVarsString, outputVarsId, maxExprString, maxExprId, inputConstraints))
    } catch {
      case e: UnsatisfiableConstraintException  => None
      case e: UnknownConstraintException        => None
    }
  }

  def findAllExec(progString : String, progId : Int, exprString : String, exprId : Int, outputVarsString : String, outputVarsId : Int, inputConstraints : Expr) : Iterator[Seq[Expr]] = {
    val program    = deserialize[Program](progString, progId)
    val expr       = deserialize[Expr](exprString, exprId)
    val outputVars = deserialize[Seq[Identifier]](outputVarsString, outputVarsId)

    findAllExec(program, expr, outputVars, inputConstraints)
  }

  private def findAllExec(program : Program, expr : Expr, outputVars : Seq[Identifier], inputConstraints : Expr) : Iterator[Seq[Expr]] = {
    val modelIterator = solutionsIterator(program, expr, inputConstraints, outputVars.toSet)
    val exprIterator  = modelIterator.map(model => outputVars.map(id => model(id)))

    exprIterator
  }

  def findAllMinimizingExec(progString : String, progId : Int, exprString : String, exprId : Int, outputVarsString : String, outputVarsId : Int, minExprString : String, minExprId : Int, inputConstraints : Expr) : Iterator[Seq[Expr]] = {
    val program    = deserialize[Program](progString, progId)
    val expr       = deserialize[Expr](exprString, exprId)
    val outputVars = deserialize[Seq[Identifier]](outputVarsString, outputVarsId)
    val minExpr    = deserialize[Expr](minExprString, minExprId)

    findAllMinimizingExec(program, expr, outputVars, minExpr, None, inputConstraints)
  }

  private def findAllMinimizingExec(program : Program, expr : Expr, outputVars : Seq[Identifier], minExpr : Expr, minExprBound : Option[Int], inputConstraints : Expr) : Iterator[Seq[Expr]] = {
    try {
      val toCheck = minExprBound match {
        case None => expr
        case Some(b) => And(expr, GreaterThan(minExpr, IntLiteral(b)))
      }
      // purescala.Settings.reporter.info("Now calling findAllMinimizing with " + toCheck)
      val minValue = chooseMinimizingModelAndValue(program, toCheck, outputVars, minExpr, inputConstraints)._2

      val minValConstraint    = And(expr, Equals(minExpr, IntLiteral(minValue)))
      val minValModelIterator = solutionsIterator(program, minValConstraint, inputConstraints, outputVars.toSet)
      val minValExprIterator  = minValModelIterator.map(model => outputVars.map(id => model(id)))

      minValExprIterator ++ findAllMinimizingExec(program, expr, outputVars, minExpr, Some(minValue), inputConstraints)
    } catch {
      case e: UnsatisfiableConstraintException  => Iterator[Seq[Expr]]()
      case e: UnknownConstraintException        => Iterator[Seq[Expr]]()
    }
  }

  private def modelValue(varId: Identifier, model: Map[Identifier, Expr]) : Expr = model.get(varId) match {
    case Some(value) => value
    case None => simplestValue(varId.getType)
  }

  def skipCounter(i : Int) : Unit = {
    purescala.Common.FreshIdentifier.forceSkip(i)
  }

  def inputVar(inputVarList : List[Variable], varName : String) : Variable = {
    inputVarList.find(_.id.name == varName).getOrElse(scala.Predef.error("Could not find input variable '" + varName + "' in list " + inputVarList))
  }

  /** Returns an iterator of interpretations for each identifier in the specified set */
  private def solutionsIterator(program : Program, predicate : Expr, inputEqualities : Expr, outputVariables : Set[Identifier]) : Iterator[Map[Identifier, Expr]] = {
    val solver = newSolver()
    solver.setProgram(program)
    solver.restartZ3

    new Iterator[Map[Identifier, Expr]] {

      // If nextModel is None, we do not know yet whether there is a next element
      var nextModel: Option[Option[Map[Identifier, Expr]]] = None

      // We add after finding each model the negation of the previous one
      var addedNegations: Expr = BooleanLiteral(true)

      var toCheck: Expr = And(inputEqualities, predicate)

      override def hasNext : Boolean = nextModel match {
        case None => 
          // Check whether there are any more models
          val (outcome, model) = solver.decideWithModel(toCheck, false)
          val toReturn = (outcome match {
            case Some(false) =>
              // there is a solution, we need to complete model for nonmentioned variables
              val completeModel = outputVariables.foldLeft(model){
                case (modelSoFar, ov) => modelSoFar.get(ov) match {
                  case None =>
                    // model has to be augmented for ov
                    modelSoFar + (ov -> simplestValue(ov.getType))
                  case _ =>
                    modelSoFar
                }
              }
              nextModel = Some(Some(completeModel))
              val newModelEqualities = And(outputVariables.map(ov => Equals(Variable(ov), completeModel(ov))).toList)
              toCheck = negate(newModelEqualities)
              true
            case Some(true) =>
              // there are definitely no more solutions
              nextModel = Some(None)
              false
            case None =>
              // unknown
              nextModel = Some(None)
              false
          })
          toReturn
        case Some(None) =>
          // There are no more models
          false
        case Some(Some(map)) =>
          true
      }

      override def next() : Map[Identifier, Expr] = nextModel match {
        case None => {
          // Let's compute the next model
          val (outcome, model) = solver.decideWithModel(toCheck, false)
          val toReturn = (outcome match {
            case Some(false) =>
              // there is a solution, we need to complete model for nonmentioned variables
              val completeModel = outputVariables.foldLeft(model){
                case (modelSoFar, ov) => modelSoFar.get(ov) match {
                  case None =>
                    // model has to be augmented for ov
                    modelSoFar + (ov -> simplestValue(ov.getType))
                  case _ =>
                    modelSoFar
                }
              }

              val newModelEqualities = And(outputVariables.map(ov => Equals(Variable(ov), completeModel(ov))).toList)
              toCheck = negate(newModelEqualities)
              completeModel
            case Some(true) =>
              // Definitely no more solutions
              throw new Exception("Requesting a new model while there are no more")
            case None =>
              // Unknown
              throw new Exception("Requesting a new model while there are no more")
          })
          toReturn
        }
        case Some(Some(m)) =>
          nextModel = None
          m
        case Some(None) =>
          throw new Exception("Requesting a new model while the last result was unknown")
      }
    }
  }
}
