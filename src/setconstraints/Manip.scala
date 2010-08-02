package setconstraints

import setconstraints.Trees._

object Manip {

  def map(s: SetType, f: (SetType) => SetType): SetType = s match {
    case EmptyType | UniversalType | VariableType(_) => f(s)
    case UnionType(sts) => f(UnionType(sts.map(s => map(s, f))))
    case IntersectionType(sts) => f(IntersectionType(sts.map(s => map(s, f))))
    case ComplementType(s) => f(ComplementType(map(s, f)))
    case ConstructorType(n@_, sts) => f(ConstructorType(n, sts.map(s => map(s, f))))
    case FunctionType(s1, s2) => {
      val ns1 = map(s1, f)
      val ns2 = map(s2, f)
      f(FunctionType(ns1, ns2))
    }
    case TupleType(sts) => f(TupleType(sts.map(s => f(s))))
  }
  def map(f: Formula, ff: (Formula) => Formula, ft: (SetType) => SetType): Formula = f match {
    case And(fs) => ff(And(fs.map(f => map(f, ff, ft))))
    case Include(s1, s2) => {
      val ns1 = map(s1, ft)
      val ns2 = map(s2, ft)
      ff(Include(ns1, ns2))
    }
    case Equals(s1, s2) => {
      val ns1 = map(s1, ft)
      val ns2 = map(s2, ft)
      ff(Equals(ns1, ns2))
    }
  }

  def flatten(formula: Formula): Formula = {
    def flatten0(f: Formula) = f match {
      case And(fs) => And(fs.flatMap{
          case And(fs2) => fs2
          case f => List(f)
        })
      case f => f
    }
    map(formula, flatten0, s => s)
  }
  def flatten(setType: SetType): SetType = {
    def flatten0(s: SetType) = s match {
      case UnionType(sts) => UnionType(sts.flatMap{
          case UnionType(sts2) => sts2
          case s => List(s)
        })
      case IntersectionType(sts) => IntersectionType(sts.flatMap{
          case IntersectionType(sts2) => sts2
          case s => List(s)
        })
      case s => s
    }
    map(setType, flatten0)
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
