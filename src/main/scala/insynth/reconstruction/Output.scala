package insynth.reconstruction

import insynth.structures.Weight._
import leon.purescala.Trees.Expr

/**
 * Encapsulation of the result output from the reconstruction phase, non UI dependent
 */
case class Output(snippet: Expr, weight: Weight){
  def getSnippet = snippet
  def getWeight = weight
}