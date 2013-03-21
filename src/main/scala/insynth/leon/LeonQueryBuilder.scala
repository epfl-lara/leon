package insynth.leon

import insynth.leon.loader.DeclarationFactory
import insynth.structures.{ SuccinctType, Const, Arrow, TSet }
import insynth.engine.InitialSender
import insynth.interfaces.QueryBuilder

import leon.purescala.TypeTrees.{ TypeTree => LeonType, _ }
import leon.purescala.Common.FreshIdentifier
import leon.purescala.Definitions.AbstractClassDef

import CommonTypes._

class LeonQueryBuilder(leonGoalType: LeonType) extends QueryBuilder(TypeTransformer(leonGoalType)) {
  	  
  val leonRetType = LeonBottomType
  val leonType = FunctionType(List(leonGoalType), leonRetType)
  
  val inSynthRetType = InSynthBottomType
  val inSynthType = Arrow(TSet(tpe), inSynthRetType)
  
  def getQuery = LeonQuery(inSynthRetType, new LeonDeclaration(QueryExpression, inSynthType, leonType), new InitialSender())
  
}