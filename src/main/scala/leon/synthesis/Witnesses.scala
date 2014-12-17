package leon.synthesis

import leon.purescala._
import TypeTrees._
import Definitions.TypedFunDef
import Extractors._
import Trees.Expr


object Witnesses {
  
  class Witness extends Expr {
    def getType = BooleanType
  }
  
  case class Guide(e : Expr) extends Witness with UnaryExtractable {
    def extract: Option[(Expr, Expr => Expr)] = Some((e, Guide))
  }
  
  case class Terminating(tfd: TypedFunDef, args: Seq[Expr]) extends Witness with NAryExtractable {    
    def extract: Option[(Seq[Expr], Seq[Expr] => Expr)] = Some((args, Terminating(tfd, _)))
  }
  
}