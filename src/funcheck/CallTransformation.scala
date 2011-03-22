package funcheck

import scala.tools.nsc.transform.TypingTransformers

trait CallTransformation 
  extends TypingTransformers
  with CodeExtraction
{
  import global._

  private lazy val funcheckPackage = definitions.getModule("funcheck")
  private lazy val cpDefinitionsModule = definitions.getModule("funcheck.CP")

  def transformCalls(unit: CompilationUnit) : Unit =
    unit.body = new CallTransformer(unit).transform(unit.body)
  
  class CallTransformer(unit: CompilationUnit) extends TypingTransformer(unit) {
    override def transform(tree: Tree) : Tree = {
      tree match {
        case a @ Apply(TypeApply(Select(s: Select, n), _), rhs @ List(predicate: Function)) if (cpDefinitionsModule == s.symbol && n.toString == "choose") => {
          println("I'm inside a choose call!")

          val Function(funValDefs, funBody) = predicate

          val fd = extractPredicate(unit, funValDefs, funBody)

          println("Here is the extracted FunDef:") 
          println(fd)

          super.transform(a)
        }

        case _ => super.transform(tree)
      }
    }
  }

}
