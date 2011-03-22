package funcheck

import scala.tools.nsc.transform.TypingTransformers
import purescala.FairZ3Solver
import purescala.DefaultReporter
import purescala.Definitions._

trait CallTransformation 
  extends TypingTransformers
  with CodeExtraction
{
  import global._

  private lazy val funcheckPackage = definitions.getModule("funcheck")
  private lazy val cpDefinitionsModule = definitions.getModule("funcheck.CP")

  private lazy val purescalaPackage = definitions.getModule("purescala")
  private lazy val fairZ3Solver = definitions.getClass("purescala.FairZ3Solver")
  private lazy val defaultReporter = definitions.getClass("purescala.DefaultReporter")

  def transformCalls(unit: CompilationUnit, prog: Program) : Unit =
    unit.body = new CallTransformer(unit, prog).transform(unit.body)
  
  class CallTransformer(unit: CompilationUnit, prog: Program) extends TypingTransformer(unit) {
    override def transform(tree: Tree) : Tree = {
      tree match {
        case a @ Apply(TypeApply(Select(s: Select, n), _), rhs @ List(predicate: Function)) if (cpDefinitionsModule == s.symbol && n.toString == "choose") => {
          println("I'm inside a choose call!")

          val Function(funValDefs, funBody) = predicate

          val fd = extractPredicate(unit, funValDefs, funBody)

          println("Here is the extracted FunDef:") 
          println(fd)

          val solverSymbol = currentOwner.newValue(NoPosition, unit.fresh.newName(NoPosition, "s")).setInfo(fairZ3Solver.tpe)
          
          val code = Block(
            ValDef(
              solverSymbol,
              New(
                Ident(fairZ3Solver),
                List(
                  List(
                    New(
                      Ident(defaultReporter),
                      List(Nil)
                    )
                  )
                )
              )
            ) :: Nil,
            Literal(Constant(0))
          )

          typer.typed(atOwner(currentOwner) {
            code
          })

          /*
          val solver = new FairZ3Solver(new DefaultReporter)
          solver.setProgram(prog)
          println(solver.decide(fd.body.get, false))
          super.transform(tree)
          */
        }

        case _ => super.transform(tree)
      }
    }
  }

}
