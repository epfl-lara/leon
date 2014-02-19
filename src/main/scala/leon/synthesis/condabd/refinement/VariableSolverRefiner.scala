package leon
package synthesis.condabd
package refinement

import scala.collection.mutable.{ Map => MutableMap }
import scala.collection.mutable.{ Set => MutableSet }

import purescala.Extractors._
import purescala.TypeTrees._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Definitions._
import purescala.Common.{ Identifier, FreshIdentifier }
import solvers._
import synthesis.Problem
import leon.evaluators._

import insynth.leon.loader._
import insynth.leon._

import _root_.insynth.util.logging.HasLogger

class VariableSolverRefiner(directSubclassMap: Map[ClassType, Set[ClassType]], variableDeclarations: Seq[LeonDeclaration],
  classMap: Map[Identifier, ClassType], solverf: SolverFactory[Solver], reporter: Reporter)
  extends VariableRefinerStructure(directSubclassMap, variableDeclarations, classMap, reporter) with HasLogger {

  val solver = SimpleSolverAPI(solverf)

  override def checkRefinements(expr: Expr, condition: Expr)(evaluator: Evaluator = null) = {
    val variables = variablesOf(expr)
    if (variables.size == 1) {
      val variable = variables.head
      variable match {
	      case oldId@IsTyped(id, AbstractClassType(cd, tps)) if variableRefinements(id).size > 1 =>
	        assert(variableRefinements(id).map(_.classDef) subsetOf cd.knownDescendents.toSet)
	        //val optCases = for (dcd <- cd.knownDescendents.sortBy(_.id.name)) yield dcd match {
	        val optCases = for (cct <- variableRefinements(id)) yield cct match {
	          case cct : CaseClassType =>
	            fine("testing variable " + id + " with condition " + condition)
	            val toSat = And(condition, CaseClassInstanceOf(cct, Variable(id)))
	            	        
	            fine("checking satisfiability of: " + toSat)
	            solver.solveSAT(toSat) match {
	              case (Some(false), _) =>
	                fine("variable cannot be of type " + cct)
	            		None
	              case _ =>
	                fine("variable can be of type " + cct)
	            		Some(cct)
	            }
	          case _ =>
	            None
	        }
	
	        val cases = optCases.flatten
	        variableRefinements(id) = variableRefinements(id) & cases.toSet
	        assert(variableRefinements(id).size == cases.size)
	          
		      List((id, variableRefinements(id).toSet))
	          
	      case id => 
	        fine("no id found for refinement that has potential refinements > 1")
	        Nil
      }
    } else {
	    fine("VariableSolverRefiner will not refine: more than one variable")
    	Nil
    }
  }

  def refineProblem(p: Problem) = {

    val newAs = p.as.map {
      case oldId @ IsTyped(id, act : AbstractClassType) =>

        val optCases = for (cct <- act.knownCCDescendents) yield {
          val toSat = And(p.pc, CaseClassInstanceOf(cct, Variable(id)))

          val isImplied = solver.solveSAT(toSat) match {
            case (Some(false), _) => true
            case _ => false
          }

          println(isImplied)

          if (!isImplied) {
            Some(cct)
          } else {
            None
          }
        }

        val cases = optCases.flatten

        println(id)
        println(cases)

        if (cases.size == 1) {
          //          id.setType(CaseClassType(cases.head))
          FreshIdentifier(oldId.name).setType(cases.head)
        } else oldId

      case id => id
    }

    p.copy(as = newAs)
  }

  override def refinePossibleTypes(refinements: List[(Identifier, Set[ClassType])]) = Unit

}
