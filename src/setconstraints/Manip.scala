package setconstraints

import setconstraints.Trees._

object Manip {

  def flatten(f: Formula): Formula = {
    def flatten0(form: Formula): Formula = form match {
      case And(fs) => {
        And(fs.foldLeft(Nil: Seq[Formula])((acc, f) => f match {
          case And(fs2) => acc ++ fs2.map(flatten0)
          case f2 => acc :+ flatten0(f2)
        }))
      }
      case f => f
    }
    Tools.fix(flatten0, f)
  }

}
