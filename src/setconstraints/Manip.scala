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
  
  def mapPreorderWhile(s: SetType, f: (SetType) => SetType, p: (SetType) => Boolean): SetType = {
    val ns = f(s) 
    if(!p(ns)) ns else ns match {
      case EmptyType | UniversalType | VariableType(_) => ns
      case UnionType(sts) => UnionType(sts.map(s => mapPreorderWhile(s, f, p)))
      case IntersectionType(sts) => IntersectionType(sts.map(s => mapPreorderWhile(s, f, p)))
      case ComplementType(s) => ComplementType(mapPreorderWhile(s, f, p))
      case ConstructorType(n@_, sts) => ConstructorType(n, sts.map(s => mapPreorderWhile(s, f, p)))
      case FunctionType(s1, s2) => {
        val ns1 = mapPreorderWhile(s1, f, p)
        val ns2 = mapPreorderWhile(s2, f, p)
        FunctionType(ns1, ns2)
      }
      case TupleType(sts) => TupleType(sts.map(s => f(s)))
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
        if (sts.exists(s1 => sts.exists(s2 => isIncompatible(s1, s2))))
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
      case ConstructorType(_, args) if args.exists(isEmptyType) => EmptyType
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

  def substitute(s: SetType, ov: VariableType, ns: SetType): SetType = mapPostorder(s, {
    case v@VariableType(_) if v == ov => ns
    case s => s
  })
  def substitute(s: SetType, maps: Map[VariableType, SetType]): SetType = mapPostorder(s, {
    case v@VariableType(_) if maps.contains(v) => maps(v)
    case s => s
  })

  def substitute(r: Relation, ov: VariableType, ns: SetType): Relation = mapPostorder(r, (f: Formula) => f, (s: SetType) => s match {
    case v@VariableType(_) if v == ov => ns
    case s => s
  }).asInstanceOf[Relation]
  def substitute(r: Relation, maps: Map[VariableType, SetType]): Relation = mapPostorder(r, (f: Formula) => f, (s: SetType) => s match {
    case v@VariableType(_) if maps.contains(v) => maps(v)
    case s => s
  }).asInstanceOf[Relation]

/*
  def dnf(s: SetType): SetType = {
    def dnf0(s: SetType) = s match {
      case EmptyType | UniversalType | VariableType(_) | ConstructorType(_, _) => UnionType(Seq(IntersectionType(Seq(s))))
      case UnionType(sts) => UnionType(sts.flatMap{
        case UnionType(sts2) => sts2
        case _ => error("not dnf")
      })
      case ComplementType(UnionType(sts)) => dnf0(IntersectionType(sts.map{
        case IntersectionType(sts2) => UnionType(sts2.map{
          case ComplementType(s) => IntersectionType(Seq(s))
          case s => IntersectionType(Seq(ComplementType(s)))
        })
        case _ => error("not dnf")
      }))
      case IntersectionType(sts) => UnionType(sts.flatMap{
        case UnionType(sts2) => 
      case _ => error("not dnf")
    }
    mapPostorder(s, dnf0)
  }
  */

  def nnf(s: SetType, constructors: Map[String, Int]): SetType = {
    def nnf0(s: SetType) = s match {
      case ComplementType(EmptyType) => UniversalType
      case ComplementType(UniversalType) => EmptyType
      case ComplementType(ComplementType(s)) => s
      case ComplementType(UnionType(sts)) => IntersectionType(sts.map(s => ComplementType(s)))
      case ComplementType(IntersectionType(sts)) => UnionType(sts.map(s => ComplementType(s)))
      case ComplementType(ConstructorType(name, sts)) =>
        UnionType(constructors.flatMap{case (n, a) => {
          if(n != name) 
            Seq(ConstructorType(n, (1 to a).map(_ => UniversalType)))
          else
            sts.zipWithIndex.map{
              case (s, i1) => ConstructorType(name, sts.zipWithIndex.map{
                case (_, i2) => if(i1 == i2) ComplementType(s) else UniversalType
              })
            }
        }}.toSeq)
      case _ => s
    }
    mapPreorder(s, nnf0)
  }

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

  def removeEquals(r: Relation): Seq[Include] = r match {
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
  private def isIncompatible(s1: SetType, s2: SetType): Boolean = (s1, s2) match {
    case (ComplementType(s1), s2) if s1 == s2 => true
    case (s1, ComplementType(s2)) if s1 == s2 => true
    case (ConstructorType(n1, _), ConstructorType(n2, _)) if n1 != n2 => true
    case _ => false
  }

}
