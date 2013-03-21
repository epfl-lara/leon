package insynth.leon

import insynth.structures.{ SuccinctType, Const, Arrow, TSet }

import leon.purescala.TypeTrees.{ TypeTree => LeonType, _ }
import leon.purescala.Common.FreshIdentifier
import leon.purescala.Definitions.AbstractClassDef

object CommonTypes {
  	
  val LeonBottomType = AbstractClassType(new AbstractClassDef(FreshIdentifier("$IDontCare$")))
  val InSynthBottomType = Const("$IDontCare$")
  
}