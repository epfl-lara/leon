package lesynth

import leon.purescala.Common.Identifier
import leon.purescala.Definitions.{ Program, FunDef }
import leon.purescala.Trees.{ Expr, Error, Hole }

object Globals {
  
  //var bodyAndPostPlug: (Expr => Expr) = _
  
  //var timeout = 2

  var allSolved: Option[Boolean] = None
  
//  var program: Option[Program] = None 
//
  var hole: Hole = _
//  
  var asMap: Map[Identifier, Expr] = _
//  
//  var holeFunDef: FunDef = _
}
