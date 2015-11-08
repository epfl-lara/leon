package leon.programsets

import leon.purescala
import purescala.Expressions._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Types._


/**
 * @author Mikael
 */
class DirectProgramSet(val p: Stream[Expr]) extends ProgramSet {
  def programs = p
}