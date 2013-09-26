package leon.synthesis.condabd.insynth.reconstruction

import insynth.structures.Weight._
import leon.purescala.Trees.Expr

/**
 * Encapsulation of the result output from the reconstruction phase, non UI dependent
 */
case class Output(snippet: Expr, weight: Weight){
  def getSnippet = snippet
  def getWeight = weight
    
	override def equals(obj:Any) = {
    obj.isInstanceOf[Output] && obj.asInstanceOf[Output].snippet == this.snippet
  }
	
}