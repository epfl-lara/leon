package leon.programsets

import leon.purescala
import purescala.Expressions._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Types._

/**
 * @author Mikael
 */
abstract class ProgramSet {
  def programs: Stream[Expr]
}