package insynth.leon

import leon.purescala.TypeTrees.{ TypeTree => LeonType }
import leon.purescala.Trees.Expr
import leon.purescala.Common.Identifier

trait ReconstructionExpression {
  	
	def getSimpleName: String
	
	override def toString = getSimpleName
  
}

case object QueryExpression extends ReconstructionExpression {
  
  def getSimpleName = "query"
  
}

case object ErrorExpression extends ReconstructionExpression {
  
  def getSimpleName = "error"  
  
}

object ImmediateExpression {
  
  def apply(id: Identifier, expr:  Expr): ImmediateExpression = ImmediateExpression(id.toString, expr)
  
}

case class ImmediateExpression( name: String, expr:  Expr ) extends ReconstructionExpression {
  
  def this(id: Identifier, expr:  Expr) = this(id.toString, expr)
  
  def apply( ) = expr
  
	def getSimpleName: String = name
  
}

object UnaryReconstructionExpression {
  
  def apply(id: Identifier, funToExpr: Expr => Expr): UnaryReconstructionExpression = UnaryReconstructionExpression(id.toString, funToExpr)
  
}

case class UnaryReconstructionExpression( name: String, funToExpr: Expr => Expr ) extends ReconstructionExpression {
  
  def this(id: Identifier, funToExpr: Expr => Expr) = this(id.toString, funToExpr)
  
  def apply( op: Expr ) = funToExpr(op)
  
	def getSimpleName: String = name
  
}

object NaryReconstructionExpression {
  
  def apply(id: Identifier, funToExpr: List[Expr] => Expr): NaryReconstructionExpression = NaryReconstructionExpression(id.toString, funToExpr)
  
}

case class NaryReconstructionExpression( name: String, funToExpr: List[Expr] => Expr ) extends ReconstructionExpression {
  
  def this(id: Identifier, funToExpr: List[Expr] => Expr) = this(id.toString, funToExpr)
  
  def apply( op: List[Expr] ) = funToExpr(op)
  
	def getSimpleName: String = name
  
}