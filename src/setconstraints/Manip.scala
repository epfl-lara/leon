package setconstraints

import setconstraints.Trees._

object Manip {

  def mapPostorder(s: SetType, f: (SetType) => SetType): SetType = s match {
    case EmptyType | UniversalType | VariableType(_) => f(s)
    case UnionType(sts) => f(UnionType(sts.map(s => mapPostorder(s, f))))
    case IntersectionType(sts) => f(IntersectionType(sts.map(s => mapPostorder(s, f))))
    case ComplementType(s) => f(ComplementType(mapPostorder(s, f)))
    case ConstructorType(n@_, sts) => f(ConstructorType(n, sts.map(s => mapPostorder(s, f))))
    case FunctionType(s1, s2) => {
      val ns1 = mapPostorder(s1, f)
      val ns2 = mapPostorder(s2, f)
      f(FunctionType(ns1, ns2))
    }
    case TupleType(sts) => f(TupleType(sts.map(s => f(s))))
  }
  def mapPostorder(f: Formula, ff: (Formula) => Formula, ft: (SetType) => SetType): Formula = f match {
    case And(fs) => ff(And(fs.map(f => mapPostorder(f, ff, ft))))
    case Include(s1, s2) => {
      val ns1 = mapPostorder(s1, ft)
      val ns2 = mapPostorder(s2, ft)
      ff(Include(ns1, ns2))
    }
    case Equals(s1, s2) => {
      val ns1 = mapPostorder(s1, ft)
      val ns2 = mapPostorder(s2, ft)
      ff(Equals(ns1, ns2))
    }
  }

  def mapPreorder(s: SetType, f: (SetType) => SetType): SetType = {
    val ns = f(s) 
    ns match {
      case EmptyType | UniversalType | VariableType(_) => ns
      case UnionType(sts) => UnionType(sts.map(s => mapPreorder(s, f)))
      case IntersectionType(sts) => IntersectionType(sts.map(s => mapPreorder(s, f)))
      case ComplementType(s) => ComplementType(mapPreorder(s, f))
      case ConstructorType(n@_, sts) => ConstructorType(n, sts.map(s => mapPreorder(s, f)))
      case FunctionType(s1, s2) => {
        val ns1 = mapPreorder(s1, f)
        val ns2 = mapPreorder(s2, f)
        FunctionType(ns1, ns2)
      }
      case TupleType(sts) => TupleType(sts.map(s => f(s)))
    }
  }
  def mapPreorder(f: Formula, ff: (Formula) => Formula, ft: (SetType) => SetType): Formula = ff(f) match {
    case And(fs) => And(fs.map(f => mapPreorder(f, ff, ft)))
    case Include(s1, s2) => {
      val ns1 = mapPreorder(s1, ft)
      val ns2 = mapPreorder(s2, ft)
      Include(ns1, ns2)
    }
    case Equals(s1, s2) => {
      val ns1 = mapPreorder(s1, ft)
      val ns2 = mapPreorder(s2, ft)
      Equals(ns1, ns2)
    }
  }
  
  def fold[A](s: SetType, z: A)(f: (A, SetType) => A): A = s match {
    case EmptyType | UniversalType | VariableType(_) => f(z, s)
    case u@UnionType(sts) => f(sts.foldLeft(z)((a, s) => fold(s, a)(f)), u)
    case i@IntersectionType(sts) => f(sts.foldLeft(z)((a, s) => fold(s, a)(f)), i)
    case c@ComplementType(s) => f(fold(s, z)(f), c)
    case c@ConstructorType(_, sts) => f(sts.foldLeft(z)((a, s) => fold(s, a)(f)), c)
    case ft@FunctionType(s1, s2) => {
      val tmp1 = fold(s1, z)(f)
      val tmp2 = fold(s2, tmp1)(f)
      f(tmp2, ft)
    }
    case t@TupleType(sts) => f(sts.foldLeft(z)((a, s) => fold(s, a)(f)), t)
  }
  def fold[A](f: Formula, z: A)(ff: (A, Formula) => A, ft: (A, SetType) => A): A = f match {
    case a@And(fs) => ff(fs.foldLeft(z)((a, f) => fold(f, a)(ff, ft)), a)
    case i@Include(s1, s2) => {
      val tmp1 = fold(s1, z)(ft)
      val tmp2 = fold(s2, tmp1)(ft)
      ff(tmp2, i)
    }
    case eq@Equals(s1, s2) => {
      val tmp1 = fold(s1, z)(ft)
      val tmp2 = fold(s2, tmp1)(ft)
      ff(tmp2, eq)
    }
  }

  def simplify(s: SetType): SetType = {
    def simplifyOne(s: SetType): SetType = s match {
      case UnionType(Seq()) => EmptyType
      case UnionType(sts) if sts.exists(isUniversalType) => UniversalType
      case u@UnionType(_) => {
        val UnionType(sts) = flatten(u)
        if(sts.exists(s1 => sts.exists(s2 => isInverse(s1, s2))))
          UniversalType
        else {
          val nsts = sts.filterNot(isEmptyType)
          nsts match {
            case Seq() => EmptyType
            case Seq(s) => s
            case _ => UnionType(nsts.distinct)
          }
        }
      }
      case IntersectionType(Seq()) => UniversalType
      case IntersectionType(sts) if sts.exists(isEmptyType) => EmptyType
      case i@IntersectionType(_) => {
        val IntersectionType(sts) = flatten(i)
        if (sts.exists(s1 => sts.exists(s2 => isInverse(s1, s2))))
          EmptyType
        else {
          val nsts = sts.filterNot(isUniversalType)
          nsts match {
            case Seq() => UniversalType
            case Seq(s) => s
            case _ => IntersectionType(nsts.distinct)
          }
        }
      }
      case ComplementType(EmptyType) => UniversalType
      case ComplementType(UniversalType) => EmptyType
      case ComplementType(ComplementType(s)) => s
      case s => s
    }
    mapPostorder(s, simplifyOne)
  }

  def vars(f: Formula): Set[String] = fold(f, Set[String]())((a, f) => a, (a, s) => s match {
    case VariableType(name) => a + name
    case _ => a
  })
  def vars(s: SetType): Set[String] = fold(s, Set[String]())((a, s) => s match {
    case VariableType(name) => a + name
    case _ => a
  })

  def constructors(f: Formula): Set[String] = fold(f, Set[String]())((a, f) => a, (a, s) => s match {
    case ConstructorType(n, _) => a + n
    case _ => a
  })
  def constructors(s: SetType): Set[String] = fold(s, Set[String]())((a, s) => s match {
    case ConstructorType(n, _) => a + n
    case _ => a
  })

  def flatten(formula: Formula): Formula = {
    def flatten0(f: Formula) = f match {
      case And(fs) => And(fs.flatMap{
          case And(fs2) => fs2
          case f => List(f)
        })
      case f => f
    }
    mapPostorder(formula, flatten0, s => s)
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
    mapPostorder(setType, flatten0)
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

  private def isUniversalType(s: SetType): Boolean = s == UniversalType
  private def isEmptyType(s: SetType): Boolean = s == EmptyType
  private def isInverse(s1: SetType, s2: SetType): Boolean = (s1, s2) match {
    case (ComplementType(s1), s2) if s1 == s2 => true
    case (s1, ComplementType(s2)) if s1 == s2 => true
    case _ => false
  }

}
