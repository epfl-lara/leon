package cp

import scala.tools.nsc.transform.TypingTransformers
import scala.tools.nsc.ast.TreeDSL
import purescala.Common.Identifier
import purescala.Definitions._
import purescala.Trees._

import Serialization._
import Terms._

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

  /** extract predicates and functions beforehand so the stored last used ID value is valid */
  def funDefMap(unit: CompilationUnit) : Map[Position,FunDef] = {
    val extracted = scala.collection.mutable.Map[Position,FunDef]()
    def extractFunDefs(tree: Tree) = tree match {
      case Apply(TypeApply(Select(Select(cpIdent, definitionsName), func2termName), typeTreeList), List(function: Function)) if 
        (definitionsName.toString == "Definitions" && func2termName.toString.matches("func2term\\d")) => {
        val Function(funValDefs, funBody) = function
        extracted += (function.pos -> extractFunction(unit, funValDefs, funBody))
      }
      case _ => 
    }
    new ForeachTreeTraverser(extractFunDefs).traverse(unit.body)

    extracted.toMap
  }

  def transformCalls(unit: CompilationUnit, prog: Program, serializedProg : Serialized) : Unit =
    unit.body = new CallTransformer(unit, prog, serializedProg).transform(unit.body)
  
  class CallTransformer(unit: CompilationUnit, prog: Program, serializedProg : Serialized) extends TypingTransformer(unit) {
    var exprToScalaSym : Symbol = null
    var exprToScalaCastSym : Symbol = null
    var scalaToExprSym : Symbol = null
    val exprSeqToScalaSyms : scala.collection.mutable.Map[List[Tree],Symbol] = scala.collection.mutable.Map[List[Tree],Symbol]()

    val extractedFunDefs : Map[Position,FunDef] = funDefMap(unit)

    private def transformHelper(tree : Tree, function : Function, codeGen : CodeGenerator) : Option[(Serialized, Serialized, Serialized, Tree, Int)] = {
      val Function(funValDefs, funBody) = function

      val fd = extractedFunDefs(function.pos)
      val outputVars : Seq[Identifier] = fd.args.map(_.id)
      
      purescalaReporter.info("Considering function:") 
      purescalaReporter.info(fd)

      fd.body match {
        case None => purescalaReporter.error("Could not extract function: " + funBody); None
        case Some(b) =>
          // serialize expression
          val serializedExpr = serialize(b)

          // compute input variables
          val inputVars : Seq[Identifier] = variablesOf(b).filter(!outputVars.contains(_)).toSeq

          purescalaReporter.info("Input variables  : " + inputVars.mkString(", "))
          purescalaReporter.info("Output variables : " + outputVars.mkString(", "))

          // serialize list of input "Variable"s
          val serializedInputVarList = serialize(inputVars map (iv => Variable(iv)))

          // serialize outputVars sequence
          val serializedOutputVars = serialize(outputVars)

          // sequence of input values
          val inputVarValues : Tree = codeGen.inputVarValues(serializedInputVarList, inputVars, scalaToExprSym)

          Some((serializedInputVarList, serializedOutputVars, serializedExpr, inputVarValues, outputVars.size))
      }
    }

    override def transform(tree: Tree) : Tree = {
      tree match {
        /** Transform implicit conversions to terms into instantiation of base terms */
        case Apply(TypeApply(Select(Select(cpIdent, definitionsName), func2termName), typeTreeList), List(function: Function)) if 
          (definitionsName.toString == "Definitions" && func2termName.toString.matches("func2term\\d")) => {
          val codeGen = new CodeGenerator(unit, currentOwner, tree.pos)

          transformHelper(tree, function, codeGen) match {
            case Some((serializedInputVarList, serializedOutputVars, serializedExpr, inputVarValues, arity)) => {
              // create constraint instance
              val code = codeGen.newBaseTerm(exprToScalaSym, serializedProg, serializedInputVarList, serializedOutputVars, serializedExpr, inputVarValues, arity)

              typer.typed(atOwner(currentOwner) {
                code
              })
            }
            case None => super.transform(tree)
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
                                      transformStats(body, tree.symbol))
                              }) 
          }
        }

        case _ => super.transform(tree)
      }
    }
  }
}
