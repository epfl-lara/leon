package leon.synthesis.condabd
package examples

import leon.purescala.Trees._
import leon.purescala.Common.{ Identifier, FreshIdentifier }

case class Example(map: Map[Identifier, Expr]) {
  
  override def toString = {
    map.toString
  }
  
}