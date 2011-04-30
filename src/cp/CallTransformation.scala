package cp

import scala.tools.nsc.transform.TypingTransformers
import scala.tools.nsc.ast.TreeDSL
import purescala.Common.Identifier
import purescala.Definitions._
import purescala.Trees._

import Serialization._
import Constraints._

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

  /** extract predicates beforehand so the stored last used ID value is valid */
  def predicateMap(unit: CompilationUnit) : Map[Position,(FunDef,Option[Expr],Option[Expr])] = {
    val extracted = scala.collection.mutable.Map[Position,(FunDef,Option[Expr],Option[Expr])]()
    def extractPredicates(tree: Tree) = tree match {
      case Apply(TypeApply(Select(Select(cpIdent, definitionsName), pred2cons1Name), typeTreeList), List(predicate: Function)) if 
        (definitionsName.toString == "Definitions" && pred2cons1Name.toString.matches("pred2cons\\d")) => {
        val Function(funValDefs, funBody) = predicate
        extracted += (predicate.pos -> extractPredicate(unit, funValDefs, funBody))
      }
      case _ => 
    }
    new ForeachTreeTraverser(extractPredicates).traverse(unit.body)

    extracted.toMap
  }

  def transformCalls(unit: CompilationUnit, prog: Program, serializedProg : Serialized) : Unit =
    unit.body = new CallTransformer(unit, prog, serializedProg).transform(unit.body)
  
  class CallTransformer(unit: CompilationUnit, prog: Program, serializedProg : Serialized) extends TypingTransformer(unit) {
    var exprToScalaSym : Symbol = null
    var exprToScalaCastSym : Symbol = null
    var scalaToExprSym : Symbol = null
    val exprSeqToScalaSyms : scala.collection.mutable.Map[List[Tree],Symbol] = scala.collection.mutable.Map[List[Tree],Symbol]()

    val extractedPredicates : Map[Position,(FunDef,Option[Expr],Option[Expr])] = predicateMap(unit)

    override def transform(tree: Tree) : Tree = {
      tree match {
        /** Transform implicit conversions to Constraint into instantiation of Constraints */
        case Apply(TypeApply(Select(Select(cpIdent, definitionsName), pred2cons1Name), typeTreeList), List(predicate: Function)) if 
          (definitionsName.toString == "Definitions" && pred2cons1Name.toString.matches("pred2cons\\d")) => {

          println("i'm in conversion from pred to constraint!")
          val Function(funValDefs, funBody) = predicate

          val (fd, minExpr, maxExpr) = extractedPredicates(predicate.pos)
          val outputVars : Seq[Identifier] = fd.args.map(_.id)
          
          purescalaReporter.info("Considering predicate:") 
          purescalaReporter.info(fd)

          val codeGen = new CodeGenerator(unit, currentOwner, tree.pos)

          fd.body match {
            case None => purescalaReporter.error("Could not extract predicate: " + funBody); super.transform(tree)
            case Some(b) =>
              // serialize expression
              val serializedExpr = serialize(b)

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
              val serializedInputVarList = serialize(inputVars map (iv => Variable(iv)))

              // serialize outputVars sequence
              val serializedOutputVars = serialize(outputVars)

              // sequence of input values
              val inputVarValues : Tree = codeGen.inputVarValues(serializedInputVarList, inputVars, scalaToExprSym)

              // create constraint instance
              val code = codeGen.newConstraint(exprToScalaSym, serializedProg, serializedInputVarList, serializedOutputVars, serializedExpr, inputVarValues, outputVars.size)

              typer.typed(atOwner(currentOwner) {
                code
              })
          }
        }

        case a @ Apply(TypeApply(Select(s: Select, n), typeTreeList), rhs @ List(constraint: Constraint)) if (cpDefinitionsModule == s.symbol && n.toString == "choose") => {
          val codeGen = new CodeGenerator(unit, currentOwner, tree.pos)

          val serializedConstraint = serialize(constraint)

          val exprSeqTree = codeGen.chooseExecCode(serializedProg, serializedConstraint)
          
          typer.typed(atOwner(currentOwner) {
            exprSeqToScalaSyms(typeTreeList) APPLY exprSeqTree
          })
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
              val serializedExpr = serialize(b)
              
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
              val serializedInputVarList = serialize(inputVars map (iv => Variable(iv)))

              // serialize outputVars sequence
              val serializedOutputVars = serialize(outputVars)

              // input constraints
              val inputConstraints : Seq[Tree] = (for (iv <- inputVars) yield {
                codeGen.inputEquality(serializedInputVarList, iv, scalaToExprSym)
              })

              val inputConstraintsConjunction = if (inputVars.isEmpty) codeGen.trueLiteral else codeGen.andExpr(inputConstraints)

              val exprSeqOptionTree = (minExpr, maxExpr) match {
                case (None, None) => {
                  codeGen.findExecCode(serializedProg, serializedExpr, serializedOutputVars, inputConstraintsConjunction)
                }
                case (Some(minE), None) => {
                  val serializedMinExpr = serialize(minE)
                  codeGen.findMinimizingExecCode(serializedProg, serializedExpr, serializedOutputVars, serializedMinExpr, inputConstraintsConjunction)
                }
                case (None, Some(maxE)) => {
                  val serializedMaxExpr = serialize(maxE)
                  codeGen.findMaximizingExecCode(serializedProg, serializedExpr, serializedOutputVars, serializedMaxExpr, inputConstraintsConjunction)
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
              val serializedExpr = serialize(b)
              
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
              val serializedInputVarList = serialize(inputVars map (iv => Variable(iv)))

              // serialize outputVars sequence
              val serializedOutputVars = serialize(outputVars)

              // input constraints
              val inputConstraints : Seq[Tree] = (for (iv <- inputVars) yield {
                codeGen.inputEquality(serializedInputVarList, iv, scalaToExprSym)
              })

              val inputConstraintsConjunction = if (inputVars.isEmpty) codeGen.trueLiteral else codeGen.andExpr(inputConstraints)

              val exprSeqIteratorTree = (minExpr, maxExpr) match {
                case (None, None) =>
                  codeGen.findAllExecCode(serializedProg, serializedExpr, serializedOutputVars, inputConstraintsConjunction)
                case (Some(minE), None) =>
                  val serializedMinExpr = serialize(minE)
                  codeGen.findAllMinimizingExecCode(serializedProg, serializedExpr, serializedOutputVars, serializedMinExpr, inputConstraintsConjunction)
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

          val (scalaToExprCode, s2eSym)                                     = codeGen.scalaToExprMethod(cd.symbol, prog, serializedProg)
          scalaToExprSym      = s2eSym

          val skipCounter                                                   = codeGen.skipCounter(purescala.Common.FreshIdentifier.last)

          val serializedSettings = serialize(new RuntimeSettings)
          val copySettings                                                  = codeGen.copySettings(serializedSettings)

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
                                      typer.typed(atOwner(currentOwner) {copySettings}) ::
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
