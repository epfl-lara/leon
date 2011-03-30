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

    def outputAssignmentList(outputVars: List[String], model: Map[Identifier, Expr]) : List[Any] = {
      val modelWithStrings = model.map{ case (k, v) => (k.name, v) }
      outputVars.map(ov => (modelWithStrings.get(ov) match {
        case Some(value) => value
        case None => scala.Predef.error("Did not find assignment for variable '" + ov + "'")
      }))
    }

    override def transform(tree: Tree) : Tree = {
      tree match {
        case a @ Apply(TypeApply(Select(s: Select, n), _), rhs @ List(predicate: Function)) if (cpDefinitionsModule == s.symbol && n.toString == "choose") => {
          val Function(funValDefs, funBody) = predicate

          val fd = extractPredicate(unit, funValDefs, funBody)

          val outputVarList = funValDefs.map(_.name.toString)
          println("Here is the output variable list: " + outputVarList.mkString(", "))
          val outputVarListFilename = writeObject(outputVarList)

          println("Here is the extracted FunDef:") 
          println(fd)
          val codeGen = new CodeGenerator(unit, currentOwner)

          fd.body match {
            case None => println("Could not extract choose predicate: " + funBody); super.transform(tree)
            case Some(b) =>
              val exprFilename = writeObject(b)
              val (programGet, progSym) = codeGen.getProgram(programFilename)
              val (exprGet, exprSym) = codeGen.getExpr(exprFilename)
              val (outputVarListGet, outputVarListSym) = codeGen.getOutputVarList(outputVarListFilename)
              val solverInvocation = codeGen.invokeSolver(progSym, exprSym)
              val exprToScalaInvocation = codeGen.invokeExprToScala(exprToScalaSym)

              val code = BLOCK(programGet, exprGet, outputVarListGet, solverInvocation, exprToScalaInvocation)

              typer.typed(atOwner(currentOwner) {
                code
              })
          }
        }

        case cd @ ClassDef(mods, name, tparams, impl) if (cd.symbol.isModuleClass && tparams.isEmpty && !cd.symbol.isSynthetic) => {
          val codeGen = new CodeGenerator(unit, currentOwner)

          val (e2sSym, e2sCode) = codeGen.exprToScala(cd.symbol, prog)
          exprToScalaSym = e2sSym
          exprToScalaCode = e2sCode
          atOwner(tree.symbol) {
            treeCopy.ClassDef(tree, transformModifiers(mods), name,
                              transformTypeDefs(tparams), impl match {
                                case Template(parents, self, body) =>
                                  treeCopy.Template(impl, transformTrees(parents),
                                    transformValDef(self), typer.typed(atOwner(currentOwner) {exprToScalaCode}) :: transformStats(body, tree.symbol))
                              }) 
          }
        }

        case _ => super.transform(tree)
      }
    }
  }

}
