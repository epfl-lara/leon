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

  private lazy val cpPackage            = definitions.getModule("cp")
  private lazy val cpDefinitionsModule  = definitions.getModule("cp.Definitions")
  private lazy val lIteratorClass       = definitions.getClass("cp.LTrees.LIterator")
  private lazy val withFilter2Function  = definitions.getMember(lIteratorClass, "withFilter2")
  private lazy val lClassSym            = definitions.getClass("cp.LTrees.L")

  private def isLSym(sym: Symbol): Boolean = {
    sym == lClassSym
  }

  private def isLIterator(sym: Symbol): Boolean = {
    sym == lIteratorClass
  }

  private def hasLIteratorType(tr: Tree): Boolean = tr.tpe match {
    case TypeRef(_, sym, _) if isLIterator(sym) => true
    case _ => false
  }

  val purescalaReporter = 
    if (Settings.verbose) purescala.Settings.reporter 
    else new purescala.QuietReporter

  /** extract predicates and functions beforehand so the stored last used ID value is valid */
  def funDefMap(unit: CompilationUnit) : Map[Position,FunDef] = {
    val extracted = scala.collection.mutable.Map[Position,FunDef]()
    def extractFunDefs(tree: Tree) = tree match {
      case Apply(TypeApply(Select(Select(cpIdent, definitionsName), func2termName), typeTreeList), List(function: Function)) if 
        (definitionsName.toString == "Definitions" && func2termName.toString.matches("func2term\\d")) => {
        val Function(funValDefs, funBody) = function
        extracted += (function.pos -> extractFunction(unit, funValDefs, funBody))
      }
      case Apply(Select(lhs, withFilterName), List(predicate: Function)) if withFilterName.toString == "withFilter" && hasLIteratorType(lhs) => {
        val Function(funValDefs, funBody) = predicate
        extracted += (predicate.pos -> extractWithFilterPredicate(unit, funValDefs, funBody))
      }
      case Apply(Select(lhs, boolean2constraint0Name), List(b: Tree)) if boolean2constraint0Name.toString == "boolean2constraint0" => {
        extracted += (b.pos -> extractFunction(unit, Nil, b))
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

    private def transformHelper(tree : Tree, function : Tree, codeGen : CodeGenerator) : Option[(Serialized, Serialized, Serialized, Serialized, Tree, Tree, Tree, Int)] = {
      val fd = extractedFunDefs(function.pos)
      val outputVars : Seq[Identifier] = fd.args.map(_.id)
      
      purescalaReporter.info("Considering function:") 
      purescalaReporter.info(fd)

      fd.body match {
        case None => purescalaReporter.error("Could not extract : " + function); None
        case Some(b) =>
          // serialize expression
          val serializedExpr = serialize(matchToIfThenElse(b))

          // compute input variables
          val nonOutputIdentifiers : Seq[Identifier] = variablesOf(b).filter(!outputVars.contains(_)).toSeq
          val reverseLVars = reverseLvarSubsts
          val (lvarIdentifiers, inputIdentifiers) = nonOutputIdentifiers.partition(id => reverseLVars.isDefinedAt(Variable(id)))

          purescalaReporter.info("Input variables  : " + inputIdentifiers.mkString(", "))
          purescalaReporter.info("Output variables : " + outputVars.mkString(", "))

          // list of input "Variables" and list of L "Variables"
          val inputVars = inputIdentifiers map (iv => Variable(iv))
          val lVars     = lvarIdentifiers map (lv => Variable(lv))

          // serialize the above
          val serializedInputVarList  = serialize(inputVars)
          val serializedLVarList      = serialize(lVars)

          // serialize outputVars sequence
          val serializedOutputVars = serialize(outputVars)

          // sequence of input values
          val inputVarValues : Tree = codeGen.inputVarValues(serializedInputVarList, inputIdentifiers, scalaToExprSym)
          val lVarValues     : Tree = codeGen.lVarValues(serializedLVarList, lvarIdentifiers, scalaToExprSym)

          val actualLVars    : Tree = codeGen.lVars(lvarIdentifiers)

          Some((serializedInputVarList, serializedLVarList, serializedOutputVars, serializedExpr, inputVarValues, lVarValues, actualLVars, outputVars.size))
      }
    }

    override def transform(tree: Tree) : Tree = {
      tree match {
        /** Transform implicit conversions to terms into instantiation of base terms */
        case Apply(TypeApply(Select(Select(cpIdent, definitionsName), func2termName), typeTreeList), List(function: Tree)) if 
          (definitionsName.toString == "Definitions" && func2termName.toString.matches("func2term\\d")) => {
          val codeGen = new CodeGenerator(unit, currentOwner, tree.pos)

          transformHelper(tree, function, codeGen) match {
            case Some((serializedInputVarList, serializedLVarList, serializedOutputVars, serializedExpr, inputVarValues, lVarValues, actualLVars, arity)) => {
              // create constraint instance
              val code = codeGen.newBaseTerm(exprToScalaSym, serializedProg, serializedInputVarList, serializedLVarList, serializedOutputVars, serializedExpr, inputVarValues, lVarValues, actualLVars, function, typeTreeList, arity)

              typer.typed(atOwner(currentOwner) {
                code
              })
            }
            case None => super.transform(tree)
          }
        }
        case Apply(Select(Select(cpIdent, definitionsName), boolean2constraint0Name), List(function: Tree)) if 
          (definitionsName.toString == "Definitions" && boolean2constraint0Name.toString.matches("boolean2constraint0")) => {
          val codeGen = new CodeGenerator(unit, currentOwner, tree.pos)

          transformHelper(tree, function, codeGen) match {
            case Some((serializedInputVarList, serializedLVarList, serializedOutputVars, serializedExpr, inputVarValues, lVarValues, actualLVars, arity)) => {
              // create constraint instance
              val code = codeGen.newBaseTerm(exprToScalaSym, serializedProg, serializedInputVarList, serializedLVarList, serializedOutputVars, serializedExpr, inputVarValues, lVarValues, actualLVars, NULL, List(TypeTree(definitions.BooleanClass.tpe)), arity)

              typer.typed(atOwner(currentOwner) {
                code
              })
            }
            case None => super.transform(tree)
          }
        }
        case Apply(Select(lhs, withFilterName), List(predicate: Function)) if withFilterName.toString == "withFilter" && hasLIteratorType(lhs) => {
          val codeGen = new CodeGenerator(unit, currentOwner, tree.pos)

          val Function(funValDefs, _) = predicate
          assert(funValDefs.size == 1)
          val constraintParamType = TypeTree(funValDefs.head.tpt.tpe match {
            case TypeRef(_, sym, List(paramTpe)) if isLSym(sym) => paramTpe
            case errorType => sys.error("unexpected type for withFilter predicate parameter: " + errorType)
          })
          val typeTreeList = List(constraintParamType, TypeTree(definitions.BooleanClass.tpe))

          transformHelper(tree, predicate, codeGen) match {
            case Some((serializedInputVarList, serializedLVarList, serializedOutputVars, serializedExpr, inputVarValues, lVarValues, actualLVars, arity)) => {
              // create constraint instance
              val termCode = codeGen.newBaseTerm(exprToScalaSym, serializedProg, serializedInputVarList, serializedLVarList, serializedOutputVars, serializedExpr, inputVarValues, lVarValues, actualLVars, NULL, typeTreeList, arity)
              val code = (lhs DOT withFilter2Function) APPLY (Function(funValDefs,termCode) setSymbol predicate.symbol)

              typer.typed(atOwner(currentOwner) {
                code
              })
            }
            case None => super.transform(tree)
          }
        }

        // Insert generated method definitions
        case cd @ ClassDef(mods, name, tparams, impl) if (cd.symbol.isModuleClass && tparams.isEmpty && !cd.symbol.isSynthetic) => {
          val codeGen = new CodeGenerator(unit, currentOwner, impl.pos)

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
