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

  def transformCalls(unit: CompilationUnit, prog: Program, programFilename: String) : Unit =
    unit.body = new CallTransformer(unit, prog, programFilename).transform(unit.body)
  
  class CallTransformer(unit: CompilationUnit, prog: Program, programFilename: String) extends TypingTransformer(unit) {
    var exprToScalaSym : Symbol = null
    var exprToScalaCode : Tree = null
    var exprToScalaCastSym : Symbol = null
    var exprToScalaCastCode : Tree = null


    override def transform(tree: Tree) : Tree = {
      tree match {
        case a @ Apply(TypeApply(Select(s: Select, n), typeTreeList), rhs @ List(predicate: Function)) if (cpDefinitionsModule == s.symbol && n.toString == "choose") => {
          val Function(funValDefs, funBody) = predicate

          val fd = extractPredicate(unit, funValDefs, funBody)

          val outputVarList = funValDefs.map(_.name.toString)
          println("Here is the output variable list: " + outputVarList.mkString(", "))
          val outputVarListFilename = writeObject(outputVarList)

          println("Here is the extracted FunDef:") 
          println(fd)
          val codeGen = new CodeGenerator(unit, currentOwner, tree.pos)

          fd.body match {
            case None => println("Could not extract choose predicate: " + funBody); super.transform(tree)
            case Some(b) =>
              // write expression into a file
              val exprFilename = writeObject(b)

              // retrieve program, expression, and list of output variables
              val (programAssignment, progSym)                = codeGen.assignProgram(programFilename)
              val (exprAssignment, exprSym)                   = codeGen.assignExpr(exprFilename)
              val (outputVarListAssignment, outputVarListSym) = codeGen.assignOutputVarList(outputVarListFilename)

              // invoke solver and get ordered list of assignments
              val (solverInvocation, outcomeTupleSym)         = codeGen.invokeSolver(progSym, exprSym)
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

              val code = BLOCK(List(programAssignment, exprAssignment, outputVarListAssignment) ::: solverInvocation ::: List(modelAssignment) ::: valueAssignments ::: List(returnExpr) : _*)

              typer.typed(atOwner(currentOwner) {
                code
              })
          }
        }

        case cd @ ClassDef(mods, name, tparams, impl) if (cd.symbol.isModuleClass && tparams.isEmpty && !cd.symbol.isSynthetic) => {
          val codeGen = new CodeGenerator(unit, currentOwner, tree.pos)

          val ((e2sSym, e2sCode), (e2sCastSym,e2sCastCode)) = codeGen.exprToScalaMethods(cd.symbol, prog)
          exprToScalaSym      = e2sSym
          exprToScalaCode     = e2sCode
          exprToScalaCastSym  = e2sCastSym
          exprToScalaCastCode = e2sCastCode

          atOwner(tree.symbol) {
            treeCopy.ClassDef(tree, transformModifiers(mods), name,
                              transformTypeDefs(tparams), impl match {
                                case Template(parents, self, body) =>
                                  treeCopy.Template(impl, transformTrees(parents),
                                    transformValDef(self), typer.typed(atOwner(currentOwner) {exprToScalaCode}) ::
                                      typer.typed(atOwner(currentOwner) {exprToScalaCastCode}) :: transformStats(body, tree.symbol))
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

}
