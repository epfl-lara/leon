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
  private lazy val cpDefinitionsModule = definitions.getModule("cp.CP")

  def transformCalls(unit: CompilationUnit, prog: Program, serializedProgString : String, serializedProgId : Int) : Unit =
    unit.body = new CallTransformer(unit, prog, serializedProgString, serializedProgId).transform(unit.body)
  
  class CallTransformer(unit: CompilationUnit, prog: Program, serializedProgString: String, serializedProgId : Int) extends TypingTransformer(unit) {
    var exprToScalaSym : Symbol = null
    var exprToScalaCastSym : Symbol = null
    var scalaToExprSym : Symbol = null

    override def transform(tree: Tree) : Tree = {
      tree match {
        case a @ Apply(TypeApply(Select(s: Select, n), typeTreeList), rhs @ List(predicate: Function)) if (cpDefinitionsModule == s.symbol && n.toString == "choose") => {
          val Function(funValDefs, funBody) = predicate

          val fd = extractPredicate(unit, funValDefs, funBody)

          val outputVarList = funValDefs.map(_.name.toString)
          println("Output variables: " + outputVarList.mkString(", "))

          println("Extracted function definition:") 
          println(fd)
          val codeGen = new CodeGenerator(unit, currentOwner, tree.pos)

          fd.body match {
            case None => println("Could not extract choose predicate: " + funBody); super.transform(tree)
            case Some(b) =>
              // write expression into a file
              val (exprString, exprId) = serialize(b)

              // retrieve program, expression
              val (progAssignment, progSym)                   = codeGen.assignProgram(serializedProgString, serializedProgId)
              val (exprAssignment, exprSym)                   = codeGen.assignExpr(exprString, exprId)

              // compute input variables and assert equalities
              val inputVars = variablesOf(b).filter{ v => !outputVarList.contains(v.name) }.toList
              println("Input variables: " + inputVars.mkString(", "))
              val (inputVarListString, inputVarListId) = serialize(inputVars map (iv => Variable(iv)))
              val equalities : List[Tree] = (for (iv <- inputVars) yield {
                codeGen.inputEquality(inputVarListString, inputVarListId, iv, scalaToExprSym)
              }).toList

              val (andExprAssignment, andExprSym) = codeGen.assignAndExpr((ID(exprSym) :: equalities) : _*)

              // invoke solver and get ordered list of assignments
              val (solverInvocation, outcomeTupleSym)         = codeGen.invokeSolver(progSym, if (inputVars.isEmpty) exprSym else andExprSym)
              val (modelAssignment, modelSym)                 = codeGen.assignModel(outcomeTupleSym)

              // TODO generate all correct e2s invocations
              val tripleList = (for ((ov, tt) <- (outputVarList zip typeTreeList)) yield {
                // declare modelValue : Expr
                val (modelValueAssignment, modelValueSym)     = codeGen.assignModelValue(ov, modelSym)
                // declare castedValue : type of argument ov
                val (scalaValueAssignment, scalaValueSym)     = codeGen.assignScalaValue(exprToScalaCastSym, tt, modelValueSym)
                (modelValueAssignment, scalaValueAssignment, scalaValueSym)
              })

              val valueAssignments = tripleList.map{ case (mva, sva, _) => List(mva, sva) }.flatten
              val returnExpressions = tripleList.map{ case(_,_,svs) => svs }

              val returnExpr : Tree = if (outputVarList.size == 1) Ident(returnExpressions.head) else {
                val tupleTypeTree = TypeTree(definitions.tupleType(typeTreeList map (tt => tt.tpe)))
                New(tupleTypeTree,List(returnExpressions map (Ident(_))))
              }

              val code = BLOCK(List(progAssignment, exprAssignment, andExprAssignment) ::: solverInvocation ::: List(modelAssignment) ::: valueAssignments ::: List(returnExpr) : _*)

              typer.typed(atOwner(currentOwner) {
                code
              })
          }
        }

        case cd @ ClassDef(mods, name, tparams, impl) if (cd.symbol.isModuleClass && tparams.isEmpty && !cd.symbol.isSynthetic) => {
          val codeGen = new CodeGenerator(unit, currentOwner, tree.pos)

          val ((e2sSym, exprToScalaCode), (e2sCastSym,exprToScalaCastCode)) = codeGen.exprToScalaMethods(cd.symbol, prog)
          exprToScalaSym      = e2sSym
          exprToScalaCastSym  = e2sCastSym

          val (scalaToExprCode, s2eSym)                                     = codeGen.scalaToExprMethod(cd.symbol, prog, serializedProgString, serializedProgId)
          scalaToExprSym      = s2eSym

          val skipCounter                                                   = codeGen.skipCounter(codeGen.getProgram(serializedProgString, serializedProgId))

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
                                      transformStats(body, tree.symbol))
                              }) 
          }
        }

        case _ => super.transform(tree)
      }
    }
  }
}

object CallTransformation {
  /* Get list of assignments in the order specified by outputVars list */
  def outputAssignments(outputVars: List[String], model: Map[Identifier, Expr]) : List[Any] = {
    val modelWithStrings = modelWithStringKeys(model)
    outputVars.map(ov => (modelWithStrings.get(ov) match {
      case Some(value) => value
      case None => scala.Predef.error("Did not find assignment for variable '" + ov + "'")
    }))
  }

  def modelValue(variable: String, model: Map[String, Expr]) : Expr = model.get(variable) match {
    case Some(value) => value
    case None => scala.Predef.error("Did not find assignment for variable '" + variable + "'")
  }

  def modelWithStringKeys(model: Map[Identifier, Expr]) : Map[String, Expr] =
    model.map{ case (k, v) => (k.name, v) }

  def model(outcomeTuple : (Option[Boolean], Map[Identifier, Expr])) : Map[String, Expr] = {
    modelWithStringKeys(outcomeTuple._2)
  }

  def outcome(outcomeTuple : (Option[Boolean], Map[Identifier, Expr])) : Option[Boolean] = {
    outcomeTuple._1
  }

  def inputVar(inputVarList : List[Variable], varName : String) : Variable = {
    inputVarList.find(_.id.name == varName).getOrElse(scala.Predef.error("Could not find input variable '" + varName + "' in list " + inputVarList))
  }

  def skipCounter(prog: Program) : Unit = {
    val maxId = prog.allIdentifiers max Ordering[Int].on[Identifier](_.id)
    purescala.Common.FreshIdentifier.forceSkip(maxId.id)
  }
}
