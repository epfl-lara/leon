/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis.condabd
package refinement

import scala.collection.mutable.{ Map => MutableMap }
import scala.collection.mutable.{ Set => MutableSet }

import leon.purescala.Extractors._
import leon.purescala.TypeTrees._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.Definitions._
import leon.purescala.Common._
import leon.evaluators._
import EvaluationResults._

import insynth.leon.loader._
import insynth.leon.{ LeonDeclaration => Declaration, _ }

import _root_.insynth.util.logging.HasLogger

class VariableRefinerExecution(variableDeclarations: Seq[Declaration],
  classMap: Map[Identifier, ClassType]) extends VariableRefiner with HasLogger {

  // map from identifier into a set of possible subclasses
  // currently only classes with no fields
  protected var variableRefinements: MutableMap[Identifier, MutableSet[ClassType]] = MutableMap.empty

  // TODO use cd.knownDescendents?
  for (varDec <- variableDeclarations) {
    varDec match {
      case Declaration(_, _, typeOfVar: ClassType, ImmediateExpression(_, IsTyped(Variable(id), AbstractClassType(cd, tps)))) =>
        variableRefinements += (id -> MutableSet(cd.knownDescendents.map(classDefToClassType(_, tps)): _*))
      case _ =>
    }
  }

  override def getPossibleTypes(id: Identifier) = variableRefinements(id).toSet

  override def checkRefinements(expr: Expr, condition: Expr)(evaluator: Evaluator = null) = {
    val variables = variablesOf(expr)

    // TODO can be extended with more variables (fix SOME values for other ones)
    if (variables.size == 1) {
      val variable = variables.head
      variable match {
        case oldId @ IsTyped(id, AbstractClassType(cd, tps)) // do not try to refine if we already know a single type is possible
        if variableRefinements(id).size > 1 =>

          assert(variableRefinements(id).map(_.classDef) subsetOf cd.knownDescendents.toSet)

          val optCases =
            for (cct <- variableRefinements(id)) yield cct match {
              case cct: CaseClassType if cct.fields.isEmpty =>

                val testValue = CaseClass(cct, Nil)
                val conditionToEvaluate = And(Not(expr), condition)
                fine("Execute condition " + conditionToEvaluate + " on variable " + id + " as " + testValue)

                evaluator.eval(conditionToEvaluate, Map(id -> testValue)) match {
                  case Successful(BooleanLiteral(false)) =>
                    fine("EvaluationSuccessful(false)")
                    fine("Refining variableRefinements(id): " + variableRefinements(id))
                    variableRefinements(id) -= cct
                    fine("Refined variableRefinements(id): " + variableRefinements(id))
                    Some(cct)
                  case Successful(BooleanLiteral(true)) =>
                    fine("EvaluationSuccessful(true)")
                    None
                  case m =>
                    warning("Eval failed: " + m)
                    None
                }

              case _ =>
                None
            }

          if (optCases.flatten.isEmpty)
            Nil
          else {
            finest("Returning: " + List((id, variableRefinements(id).toSet)))
            List((id, variableRefinements(id).toSet))
          }
        case _ =>
          fine("did not match for refinement " + variable)
          Nil
      }
    } else Nil
  }

  // inspect the expression if some refinements can be done
  def getIdAndClassDef(expr: Expr) = expr match {
    case CaseClassInstanceOf(classDef, Variable(id)) =>
      Some((id, classDef))
    case _ =>
      None
  }

  override def refinePossibleTypes(refinements: List[(Identifier, Set[ClassType])]) =
    for ((id, types) <- refinements)
      variableRefinements(id) &~= types

}
