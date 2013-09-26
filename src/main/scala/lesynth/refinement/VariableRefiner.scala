package lesynth
package refinement

import scala.collection.mutable.{Map => MutableMap}
import scala.collection.mutable.{Set => MutableSet}

import leon._
import leon.purescala.Trees._
import leon.purescala.TypeTrees._
import leon.purescala.Definitions._
import leon.purescala.Common.{ Identifier, FreshIdentifier }

import insynth.leon.loader._
import insynth.leon.{ LeonDeclaration => Declaration, _ }

import insynth.util.logging.HasLogger

// each variable of super type can actually have a subtype
// get sine declaration maps to be able to refine them  
class VariableRefiner(directSubclassMap: Map[ClassType, Set[ClassType]], variableDeclarations: Seq[Declaration],
  classMap: Map[Identifier, ClassType], reporter: Reporter) extends HasLogger {  
  
    // map from identifier into a set of possible subclasses
  protected var variableRefinements: MutableMap[Identifier, MutableSet[ClassType]] = MutableMap.empty
    for (varDec <- variableDeclarations) {
      varDec match {
        case Declaration(_, _, typeOfVar: ClassType, ImmediateExpression(_, Variable(id))) =>
          variableRefinements += (id -> MutableSet(directSubclassMap(typeOfVar).toList: _*))
        case _ =>
      }
    }    
  
  def getPossibleTypes(id: Identifier) = variableRefinements(id)
  
  def checkRefinements(expr: Expr, condition: Expr, allDeclarations: List[Declaration]) =
	  // check for refinements
	  getIdAndClassDef(expr) match {
	    case Some(refinementPair @ (id, classType)) if variableRefinements(id).size > 1 =>
	      fine("And now we have refinement type: " + refinementPair)
	      fine("variableRefinements(id) before" + variableRefinements(id))
	      variableRefinements(id) -= classMap(classType.id)
	      fine("variableRefinements(id) after" + variableRefinements(id))
	
	      // if we have a single subclass possible to refine
	      if (variableRefinements(id).size == 1) {
	        reporter.info("We do variable refinement for " + id)
	
	        val newType = variableRefinements(id).head
	        fine("new type is: " + newType)
	
	        // update declarations
	        val newDeclarations =
	          refinedDeclarations(id, newType, allDeclarations)
	        
	        (true, newDeclarations.flatten)	
	      } else {
	        fine("we cannot do variable refinement :(")
	        (false, allDeclarations)
	      }
	    case _ =>
        (false, allDeclarations)
	  }

  // inspect the expression if some refinements can be done
  def getIdAndClassDef(expr: Expr) = expr match {
    case CaseClassInstanceOf(classDef, Variable(id)) =>
      Some((id, classDef))
    case _ =>
      None
  }
  
  def refinedDeclarations(id: Identifier, newType: ClassType, allDeclarations: List[Declaration]) =
    for (dec <- allDeclarations)
      yield dec match {
        case Declaration(inSynthType, _, decClassType, imex @ ImmediateExpression(_, Variable(`id`))) =>	              
	        ((
            newType.classDef match {
              case newTypeCaseClassDef@CaseClassDef(_, parent, fields) =>
                fine("matched case class def for refinement " + newTypeCaseClassDef)
		            for (field <- fields)
				          yield Declaration(
						        ImmediateExpression(id.name + "." + field.id.name,
					            CaseClassSelector(newTypeCaseClassDef, imex.expr, field.id) ), 
						        TypeTransformer(field.id.getType), field.id.getType
					        )
              case _ =>
                Seq.empty
            }
	        ): Seq[Declaration]) :+ Declaration(imex, TypeTransformer(newType), newType)
        case _ =>
          Seq(dec)
      }
  
}
