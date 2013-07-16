package insynth.leon

import insynth.structures.SuccinctType
import insynth.interfaces.Declaration
import insynth.structures.Weight._

import leon.purescala.TypeTrees.{ TypeTree => LeonType }
import leon.purescala.Trees.Expr

case class LeonDeclaration(
	override val inSynthType: SuccinctType, override val weight: Weight,
	val leonType: LeonType, val expression: ReconstructionExpression 
)
extends Declaration(inSynthType, weight) {
      
  def this(expression: ReconstructionExpression, inSynthType: SuccinctType,
    leonType: LeonType, commutative: Boolean, weight: Weight    
  ) = {
    this(inSynthType, weight, leonType, expression)
    isCommunitative = commutative
  } 
  
  def this(expression: ReconstructionExpression, inSynthType: SuccinctType, leonType: LeonType)
  	= this(inSynthType, 1.0f, leonType, expression)
  
  var isCommunitative = false
	
  private var query = false
      
  def getDomainType = leonType
    
  def getSimpleName = expression.getSimpleName
  
  override def toString = getSimpleName + " : " + inSynthType + " : " + leonType + " [" + expression + "]"
  
}

object LeonDeclaration {
  
  def apply(expression: ReconstructionExpression, inSynthType: SuccinctType, leonType: LeonType)
  	= new LeonDeclaration(expression, inSynthType, leonType)
  
  def apply(expression: ReconstructionExpression, inSynthType: SuccinctType,
		leonType: LeonType, weight: Weight
	) =	new LeonDeclaration(inSynthType, weight, leonType, expression)
    
  def apply(expression: ReconstructionExpression, inSynthType: SuccinctType,
    leonType: LeonType, commutative: Boolean, weight: Weight    
  ) = new LeonDeclaration(expression, inSynthType, leonType, commutative, weight)
  
}