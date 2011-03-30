package cp

import scala.tools.nsc.transform.TypingTransformers
import scala.tools.nsc.ast.TreeDSL
import purescala.FairZ3Solver
import purescala.DefaultReporter
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

    override def transform(tree: Tree) : Tree = {
      tree match {
        case a @ Apply(TypeApply(Select(s: Select, n), _), rhs @ List(predicate: Function)) if (cpDefinitionsModule == s.symbol && n.toString == "choose") => {
          println("I'm inside a choose call!")

          val Function(funValDefs, funBody) = predicate

          val fd = extractPredicate(unit, funValDefs, funBody)

          println("Here is the extracted FunDef:") 
          println(fd)
          val codeGen = new CodeGenerator(unit, currentOwner)

          fd.body match {
            case None => println("Could not extract choose predicate: " + funBody); super.transform(tree)
            case Some(b) =>
              val exprFilename = writeExpr(b)
              val (programGet, progSym) = codeGen.getProgram(programFilename)
              val (exprGet, exprSym) = codeGen.getExpr(exprFilename)
              val solverInvocation = codeGen.invokeSolver(progSym, exprSym)
              val exprToScalaInvocation = codeGen.invokeExprToScala(exprToScalaSym)
              // val code = BLOCK(programGet, exprGet, solverInvocation)
              val code = BLOCK(programGet, exprGet, solverInvocation, exprToScalaInvocation)

              typer.typed(atOwner(currentOwner) {
                code
              })
          }
        }

        case cd @ ClassDef(mods, name, tparams, impl) if (cd.symbol.isModuleClass && tparams.isEmpty && !cd.symbol.isSynthetic) => {
          println("I'm inside the object " + name.toString + " !")

          val codeGen = new CodeGenerator(unit, currentOwner)
          val (e2sSym, e2sCode) = codeGen.exprToScala(cd.symbol)
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

        case dd @ DefDef(mods, name, _, _, _, _) => {
          super.transform(tree)
        }

        case _ => super.transform(tree)
      }
    }
  }

}
