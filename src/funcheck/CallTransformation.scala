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

          /*
          typer.typed(atOwner(currentOwner) {
            code
          })
          */
          super.transform(tree)

          /*
          val solver = new FairZ3Solver(new DefaultReporter)
          solver.setProgram(prog)
          println(solver.decide(fd.body.get, false))
          */
        }

        case _ => super.transform(tree)
      }
    }
  }

}
