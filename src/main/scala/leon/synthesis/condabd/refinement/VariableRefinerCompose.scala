package leon.synthesis.condabd
package refinement

import leon.purescala.Trees._
import leon.purescala.TypeTrees._
import leon.purescala.Common.{ Identifier, FreshIdentifier }
import leon.evaluators._

import insynth.leon.{ LeonDeclaration => Declaration, _ }

// TODO update other refiners with results of this one
class VariableRefinerCompose extends VariableRefiner {

  private var refiners = Array[VariableRefiner]()

  def add(refiner: VariableRefiner) = {
    refiners :+= refiner
    //    refiner.refinePossibleTypes(id, types)
    this
  }

  override def getPossibleTypes(id: Identifier) =
    refiners.head.getPossibleTypes(id)

  override def refinePossibleTypes(refinements: List[(Identifier, Set[ClassType])]) =
    for (refiner <- refiners)
      refiner.refinePossibleTypes(refinements)

  override def checkRefinements(expr: Expr, condition: Expr)(evaluator: Evaluator = null) = {
    val refineMap =
      ((Map[Identifier, Set[ClassType]]()) /: refiners) {
        case (refineMap, refiner) =>
          ( refineMap /: refiner.checkRefinements(expr, condition)(evaluator) ) {
            case (map, (id, newTypes)) =>
              if (map contains id)
                map + (id -> map(id).intersect(newTypes))
              else
                map + (id -> newTypes)
          }
      }
    
    for (refiner <- refiners)
      refiner.refinePossibleTypes(refineMap.toList)
    
    refineMap.toList
  }

}
