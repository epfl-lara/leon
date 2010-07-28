package setconstraints

import setconstraints.Trees._

object Manip {

  def flatten(f: Formula): Formula = f match {
    case And(fs) => And(fs.flatMap(f => flatten(f) match {
        case And(fs2) => fs2
        case f => List(f)
      }))
    case f => f
  }

  def includes(f: Formula): Seq[Include] = flatten(f) match {
    case And(fs) if fs.forall(isRelation) => fs.flatMap(f => removeEquals(f.asInstanceOf[Relation]))
    case f@_ => error("unexpected formula :" + f)
  }

  private def removeEquals(r: Relation): Seq[Include] = r match {
    case Equals(s1, s2) => Seq(Include(s1, s2), Include(s2, s1))
    case i@Include(_,_) => Seq(i)
  }

  private def isRelation(f: Formula): Boolean = f.isInstanceOf[Relation]

}
