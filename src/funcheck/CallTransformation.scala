package funcheck

import scala.tools.nsc.transform.TypingTransformers
import purescala.FairZ3Solver
import purescala.DefaultReporter
import purescala.Definitions._
import purescala.Trees._

trait CallTransformation 
  extends TypingTransformers
  with CodeGeneration
{
  self: CPComponent =>
  import global._

  private lazy val funcheckPackage = definitions.getModule("funcheck")
  private lazy val cpDefinitionsModule = definitions.getModule("funcheck.CP")


  def transformCalls(unit: CompilationUnit, prog: Program, filename: String) : Unit =
    unit.body = new CallTransformer(unit, prog, filename).transform(unit.body)
  
  class CallTransformer(unit: CompilationUnit, prog: Program, filename: String) extends TypingTransformer(unit) {
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
              val (readProgram, progSym) = codeGen.generateProgramRead(filename)
              val solverInvocation = codeGen.generateSolverInvocation(b, progSym)
              val code = Block(readProgram :: Nil, solverInvocation)

              typer.typed(atOwner(currentOwner) {
                code
              })
          }
        }

        case _ => super.transform(tree)
      }
    }
  }

}
