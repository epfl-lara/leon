package setconstraints

object Trees {

  sealed trait Formula

  case class And(fs: Seq[Formula]) extends Formula

  sealed abstract trait Relation extends Formula

  sealed abstract trait SetType 

  case class Include(s1: SetType, s2: SetType) extends Relation

  object Equals {
    def apply(s1: SetType, s2: SetType) = And(List(Include(s1, s2), Include(s2, s1)))
    def unapply(f: Formula): Boolean = f match {
      case And(List(Include(s1, s2), Include(s3, s4))) if s1 == s4 && s2 == s3 => true
      case _ => false
    }
  }

  case class UnionType(sets: Seq[SetType]) extends SetType
  case class IntersectionType(sets: Seq[SetType]) extends SetType
  case class FunctionType(s1: SetType, s2: SetType) extends SetType
  case class TupleType(sets: Seq[SetType]) extends SetType
  case class ConstructorType(name: String, sets: Seq[SetType]) extends SetType
  case class VariableType(name: String) extends SetType

  private var varCounter = -1
  def freshVar(name: String) = {
    varCounter += 1
    VariableType(name + "_" + varCounter)
  }

}
