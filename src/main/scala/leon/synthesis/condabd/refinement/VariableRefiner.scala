package leon.synthesis.condabd
package refinement

import leon.purescala.Trees._
import leon.purescala.TypeTrees._
import leon.purescala.Definitions._
import leon.purescala.Common.{ Identifier, FreshIdentifier }
import leon.evaluators._

import insynth.leon.{ LeonDeclaration => Declaration, _ }

import _root_.insynth.util.logging.HasLogger

// TODO a *provider* for maps from id to possible types (so that not all classes need to maintain a map)
trait VariableRefiner extends HasLogger {

  type Type = ClassType

  def getPossibleTypes(id: Identifier): Set[Type]

  def refinePossibleTypes(refinements: List[(Identifier, Set[ClassType])])

  /**
   * refine given declarations according to given expression and current partition condition
   * @param expr
   * @param condition
   * @param declarations
   * @return new declarations with refined ones
   */
  def checkRefinements(expr: Expr, condition: Expr)(evaluator: Evaluator = null): List[(Identifier, Set[ClassType])]

  def refine(expr: Expr, condition: Expr, declarations: List[Declaration], evaluator: Evaluator = null) = {
    checkRefinements(expr: Expr, condition: Expr)(evaluator: Evaluator) match {
      case Nil => (false, declarations)
      case list =>
        ((false, declarations) /: list) {
          case ((flag, refined), (id, newTypes)) =>
            fine(((flag, refined), (id, newTypes)).toString)
            if (newTypes.size == 1)
              (true, refineDeclarations(id, newTypes.head, refined))
            else
              (flag, refined)
        }
    }
  }

  def refineDeclarations(id: Identifier, newType: ClassType, allDeclarations: List[Declaration]) =
    (for (dec <- allDeclarations)
      yield dec match {
      case Declaration(inSynthType, _, decClassType, imex @ ImmediateExpression(_, Variable(`id`))) =>
        ((
          newType.classDef match {
            case newTypeCaseClassDef @ CaseClassDef(_, parent, fields) =>
              fine("matched case class def for refinement " + newTypeCaseClassDef)
              for (field <- fields)
                yield Declaration(
                ImmediateExpression(id.name + "." + field.id.name,
                CaseClassSelector(newTypeCaseClassDef, imex.expr, field.id)),
                TypeTransformer(field.id.getType), field.id.getType)
            case _ =>
              Seq.empty
          }): Seq[Declaration]) :+ Declaration(imex, TypeTransformer(newType), newType)
      case _ =>
        Seq(dec)
    }).flatten

}
