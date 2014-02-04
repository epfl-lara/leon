package leon.synthesis.condabd
package refinement

import scala.collection.mutable.{Map => MutableMap}
import scala.collection.mutable.{Set => MutableSet}

import leon._
import leon.purescala.Trees._
import leon.purescala.TypeTrees._
import leon.purescala.Definitions._
import leon.purescala.Common.{ Identifier, FreshIdentifier }
import leon.evaluators._

import insynth.leon.loader._
import insynth.leon.{ LeonDeclaration => Declaration, _ }

import _root_.insynth.util.logging.HasLogger

// each variable of super type can actually have a subtype
// get sine declaration maps to be able to refine them  
class VariableRefinerStructure(directSubclassMap: Map[ClassType, Set[ClassType]], variableDeclarations: Seq[Declaration],
  classMap: Map[Identifier, ClassType], reporter: Reporter) extends VariableRefiner with HasLogger {  
  
    // map from identifier into a set of possible subclasses
  protected var variableRefinements: MutableMap[Identifier, MutableSet[ClassType]] = MutableMap.empty
    for (varDec <- variableDeclarations) {
      varDec match {
        case Declaration(_, _, typeOfVar: ClassType, ImmediateExpression(_, Variable(id))) =>
          variableRefinements += (id -> MutableSet(directSubclassMap(typeOfVar).toList: _*))
        case _ =>
      }
    }    
  
  override def getPossibleTypes(id: Identifier) = variableRefinements(id).toSet
  
  override def checkRefinements(expr: Expr, condition: Expr)(evaluator: Evaluator = null) =
	  // check for refinements
	  getIdAndClassDef(expr) match {
	    case Some(refinementPair @ (id, classType)) if variableRefinements(id).size > 1 =>
	      fine("And now we have refinement type: " + refinementPair)
	      fine("variableRefinements(id) before" + variableRefinements(id))
	      variableRefinements(id) -= classMap(classType.id)
	      fine("variableRefinements(id) after" + variableRefinements(id))
	
	      List((id, variableRefinements(id).toSet))
	    case _ =>
          Nil
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
