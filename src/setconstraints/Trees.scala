package setconstraints

object Trees {

  sealed trait Formula

  case class And(fs: Seq[Formula]) extends Formula

  sealed abstract trait Relation extends Formula

  sealed abstract trait SetType 

  case class Include(s1: SetType, s2: SetType) extends Relation
  case class Equals(s1: SetType, s2: SetType) extends Relation

  case class UnionType(sets: Seq[SetType]) extends SetType
  case class IntersectionType(sets: Seq[SetType]) extends SetType
  case class ComplementType(st: SetType) extends SetType
  case class FunctionType(s1: SetType, s2: SetType) extends SetType
  case class TupleType(sets: Seq[SetType]) extends SetType
  case class ConstructorType(name: String, sets: Seq[SetType]) extends SetType
  case class VariableType(name: String) extends SetType
  case object EmptyType extends SetType
  case object UniversalType extends SetType

  private var varCounter = -1
  def freshVar(name: String) = {
    varCounter += 1
    VariableType(name + "_" + varCounter)
  }

}
