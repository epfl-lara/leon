package insynth.leon

import insynth.leon.loader.DeclarationFactory
import insynth.engine.InitialSender
import insynth.structures.SuccinctType
import insynth.interfaces.Query

import leon.purescala.TypeTrees._
import leon.purescala.Common.FreshIdentifier

case class LeonQuery(override val inSynthRetType: SuccinctType, decl: LeonDeclaration, sender: InitialSender)
extends Query(inSynthRetType) {
  
  def getSolution = sender.getAnswers
  
  def getDeclaration = decl
  
  def getSender = sender
  
}