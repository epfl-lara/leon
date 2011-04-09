package cp

import scala.tools.nsc.transform.TypingTransformers
import scala.tools.nsc.ast.TreeDSL
import purescala.FairZ3Solver
import purescala.DefaultReporter
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

  val reporter = purescala.Settings.reporter

  /** Collect all choose and findAll signatures in program */
  def chooseSignatures(unit: CompilationUnit) : Set[List[Tree]] = {
    val signatures : scala.collection.mutable.Set[List[Tree]] = scala.collection.mutable.Set[List[Tree]]()
    def collectSignatures(tree: Tree) = tree match {
      case Apply(TypeApply(Select(s: Select, n), typeTreeList), List(predicate: Function)) if (cpDefinitionsModule == s.symbol && (n.toString == "choose" || n.toString == "findAll")) =>
        signatures += typeTreeList
      case _ => 
    }
    new ForeachTreeTraverser(collectSignatures).traverse(unit.body)

    signatures.toSet
  }

  def transformCalls(unit: CompilationUnit, prog: Program, progString : String, progId : Int) : Unit =
    unit.body = new CallTransformer(unit, prog, progString, progId).transform(unit.body)
  
  class CallTransformer(unit: CompilationUnit, prog: Program, progString: String, progId : Int) extends TypingTransformer(unit) {
    var exprToScalaSym : Symbol = null
    var exprToScalaCastSym : Symbol = null
    var scalaToExprSym : Symbol = null
    val exprSeqToScalaSyms : scala.collection.mutable.Map[List[Tree],Symbol] = scala.collection.mutable.Map[List[Tree],Symbol]()

    override def transform(tree: Tree) : Tree = {
      tree match {
        case a @ Apply(TypeApply(Select(s: Select, n), typeTreeList), rhs @ List(predicate: Function)) if (cpDefinitionsModule == s.symbol && n.toString == "choose") => {
          val Function(funValDefs, funBody) = predicate

          val fd = extractPredicate(unit, funValDefs, funBody)
          val outputVars : Seq[Identifier] = fd.args.map(_.id)

          reporter.info("Considering predicate:") 
          reporter.info(fd)

          val codeGen = new CodeGenerator(unit, currentOwner, tree.pos)

          fd.body match {
            case None => reporter.error("Could not extract choose predicate: " + funBody); super.transform(tree)
            case Some(b) =>
              // serialize expression
              val (exprString, exprId) = serialize(b)
              
              // compute input variables
              val inputVars : Seq[Identifier] = variablesOf(b).filter(!outputVars.contains(_)).toSeq

              reporter.info("Input variables  : " + inputVars.mkString(", "))
              reporter.info("Output variables : " + outputVars.mkString(", "))

              // serialize list of input "Variable"s
              val (inputVarListString, inputVarListId) = serialize(inputVars map (iv => Variable(iv)))

              // serialize outputVars sequence
              val (outputVarsString, outputVarsId) = serialize(outputVars)

              // input constraints
              val inputConstraints : Seq[Tree] = (for (iv <- inputVars) yield {
                codeGen.inputEquality(inputVarListString, inputVarListId, iv, scalaToExprSym)
              })

              val inputConstraintsConjunction = codeGen.andExpr(inputConstraints)

              val chooseExecCall = codeGen.chooseExecCode(progString, progId, exprString, exprId, outputVarsString, outputVarsId, inputConstraintsConjunction)

              val code = BLOCK(
                (exprSeqToScalaSyms(typeTreeList)) APPLY (chooseExecCall)
              )

              typer.typed(atOwner(currentOwner) {
                code
              })
          }
        }

        case a @ Apply(TypeApply(Select(s: Select, n), typeTreeList), rhs @ List(predicate: Function)) if (cpDefinitionsModule == s.symbol && n.toString == "findAll") => {
          val Function(funValDefs, funBody) = predicate

          val fd = extractPredicate(unit, funValDefs, funBody)
          val outputVars : Seq[Identifier] = fd.args.map(_.id)

          reporter.info("Considering predicate:") 
          reporter.info(fd)

          val codeGen = new CodeGenerator(unit, currentOwner, tree.pos)

          fd.body match {
            case None => reporter.error("Could not extract choose predicate: " + funBody); super.transform(tree)
            case Some(b) =>
              // serialize expression
              val (exprString, exprId) = serialize(b)
              
              // compute input variables
              val inputVars : Seq[Identifier] = variablesOf(b).filter(!outputVars.contains(_)).toSeq

              reporter.info("Input variables  : " + inputVars.mkString(", "))
              reporter.info("Output variables : " + outputVars.mkString(", "))

              // serialize list of input "Variable"s
              val (inputVarListString, inputVarListId) = serialize(inputVars map (iv => Variable(iv)))

              // serialize outputVars sequence
              val (outputVarsString, outputVarsId) = serialize(outputVars)

              // input constraints
              val inputConstraints : Seq[Tree] = (for (iv <- inputVars) yield {
                codeGen.inputEquality(inputVarListString, inputVarListId, iv, scalaToExprSym)
              })

              val inputConstraintsConjunction = if (inputVars.isEmpty) codeGen.trueLiteral else codeGen.andExpr(inputConstraints)

              val findAllExecCall = codeGen.findAllExecCode(progString, progId, exprString, exprId, outputVarsString, outputVarsId, inputConstraintsConjunction)

              val code = BLOCK(
                findAllExecCall
              )

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

          val skipCounter                                                   = codeGen.skipCounter(progString, progId)

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

  def chooseExec(progString : String, progId : Int, exprString : String, exprId : Int, outputVarsString : String, outputVarsId : Int, inputConstraints : Expr) : Seq[Expr] = {
    val program    = deserialize[Program](progString, progId)
    val expr       = deserialize[Expr](exprString, exprId)
    val outputVars = deserialize[Seq[Identifier]](outputVarsString, outputVarsId)

    val solver = new FairZ3Solver(new DefaultReporter())
    solver.setProgram(program)

    val (outcome, model) = solver.restartAndDecideWithModel(And(expr, inputConstraints), false)

    outcome match {
      case Some(false) =>
        outputVars.map(v => modelValue(v, model))
      case Some(true) =>
        throw new UnsatisfiableConstraintException()
      case None =>
        throw new UnknownConstraintException()
    }
  }

  def findAllExec(progString : String, progId : Int, exprString : String, exprId : Int, outputVarsString : String, outputVarsId : Int, inputConstraints : Expr) : Iterator[Seq[Expr]] = {
    val program    = deserialize[Program](progString, progId)
    val expr       = deserialize[Expr](exprString, exprId)
    val outputVars = deserialize[Seq[Identifier]](outputVarsString, outputVarsId)

    val modelIterator = solutionsIterator(program, expr, inputConstraints, outputVars.toSet)
    val exprIterator  = modelIterator.map(model => outputVars.map(id => model(id)))

    exprIterator
  }

  private def modelValue(varId: Identifier, model: Map[Identifier, Expr]) : Expr = model.get(varId) match {
    case Some(value) => value
    case None => simplestValue(varId.getType)
  }

  def skipCounter(progString: String, progId : Int) : Unit = {
    val prog = deserialize[Program](progString, progId)
    val maxId = prog.allIdentifiers max Ordering[Int].on[Identifier](_.id)
    purescala.Common.FreshIdentifier.forceSkip(maxId.id)
  }

  def inputVar(inputVarList : List[Variable], varName : String) : Variable = {
    inputVarList.find(_.id.name == varName).getOrElse(scala.Predef.error("Could not find input variable '" + varName + "' in list " + inputVarList))
  }

  /** Returns an iterator of interpretations for each identifier in the specified set */
  private def solutionsIterator(program : Program, predicate : Expr, inputEqualities : Expr, outputVariables : Set[Identifier]) : Iterator[Map[Identifier, Expr]] = {
    val solver = new FairZ3Solver(new DefaultReporter())
    solver.setProgram(program)

    new Iterator[Map[Identifier, Expr]] {

      // If nextModel is None, we do not know yet whether there is a next element
      var nextModel: Option[Option[Map[Identifier, Expr]]] = None

      // We add after finding each model the negation of the previous one
      var addedNegations: Expr = BooleanLiteral(true)

      override def hasNext : Boolean = nextModel match {
        case None => 
          // Check whether there are any more models
          val toCheck = inputEqualities :: predicate :: addedNegations :: Nil
          val (outcome, model) = solver.restartAndDecideWithModel(And(toCheck), false)
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
              addedNegations = And(addedNegations, negate(newModelEqualities))
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
          val (outcome, model) = solver.restartAndDecideWithModel(And(inputEqualities :: predicate :: addedNegations :: Nil), false)
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
              addedNegations = And(addedNegations, negate(newModelEqualities))
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
