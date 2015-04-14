/* Copyright 2009-2015 EPFL, Lausanne */

package leon.synthesis

import leon.purescala._
import Types._
import Definitions.TypedFunDef
import Extractors._
import Expressions.Expr


object Witnesses {
  
  class Witness extends Expr {
    val getType = BooleanType
  }
  
  case class Guide(e : Expr) extends Witness with UnaryExtractable {
    def extract: Option[(Expr, Expr => Expr)] = Some((e, Guide))
  }
  
  case class Terminating(tfd: TypedFunDef, args: Seq[Expr]) extends Witness with NAryExtractable {    
    def extract: Option[(Seq[Expr], Seq[Expr] => Expr)] = Some((args, Terminating(tfd, _)))
  }
  
}
