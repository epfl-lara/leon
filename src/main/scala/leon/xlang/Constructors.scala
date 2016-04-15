package leon
package xlang

import purescala.Expressions._
import purescala.Types._
import xlang.Expressions._
import xlang.ExprOps._

object Constructors {

  def block(exprs: Seq[Expr]): Expr = {
    require(exprs.nonEmpty)

    val flat = exprs.flatMap{
      case Block(es2, el) => es2 :+ el
      case e2 => Seq(e2)
    }

    val init = flat.init
    val last = flat.last
    val filtered = init.filter{
      case UnitLiteral() => false
      case _ => true
    }

    val finalSeq = 
      if(last == UnitLiteral() && filtered.last.getType == UnitType) filtered else (filtered :+ last)

    finalSeq match {
      case Seq() => UnitLiteral()
      case Seq(e) => e
      case es => Block(es.init, es.last)
    }
  }

}
