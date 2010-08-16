package setconstraints

import Trees._
import Manip._

object Solver {

  def apply(system: Set[Relation], constructors: Map[String, Int]): Option[List[FixPoint]] = {
    error("TODO")
  }

  def solve(system: Set[Relation]): Option[List[Equals]] = {
    error("TODO")
  }

  def cascadingEquations(systems: Set[Set[Include]]): Set[Set[Equals]] = {
    def cascadingEquations0(system: Set[Include]): Set[Equals] = {
      val vs = vars(system)
      val nvs = vs.map(freshVar(_))
      val ts = vs.zip(nvs).map{case (v, nv) => {
        val lb = UnionType(system.flatMap{
          case Include(IntersectionType(lits), EmptyType) if !lits.isEmpty && lits.head == ComplementType(VariableType(v)) => lits.tail
          case _ => Seq()
        }.toSeq)
        val ub = IntersectionType(system.flatMap{
          case Include(IntersectionType(lits), EmptyType) if !lits.isEmpty && lits.head == VariableType(v) => 
            Seq(ComplementType(IntersectionType(lits.tail)))
          case _ => Seq()
        }.toSeq)
        UnionType(Seq(lb, IntersectionType(Seq(nv, ub))))
      }}
      val ns = vs.zip(ts).map{case (v, t) => Equals(VariableType(v), t)}
      ns.map{case Equals(v, rhs) => Equals(v, simplify(rhs))}
    }
    systems.map(cascadingEquations0)
  }

  def cascadingSystems(system: Set[Include], constructors: Map[String, Int]): Set[Set[Include]] = {

    def constructorRule(system: Set[Include]): Set[Set[Include]] = {
      val (option, rest) = extract((x: Include) => x match {
        case Include(IntersectionType(Seq(ConstructorType(_, args))), EmptyType) => true 
        case _ => false
      }, system)
      option match {
        case Some(Include(IntersectionType(Seq(ConstructorType(_, args))), EmptyType)) =>
          args.map(arg => rest + Include(arg, EmptyType)).toSet
        case None => Set(system)
        case _ => error("")
      }
    }

    def transitiveRule(system: Set[Include]): Set[Include] = {
    /*
      val (candidates, r1) = system.partition{
        case Include(IntersectionType(List(VariableType(_), _)), EmptyType) => true
        case _ => false
      }
      val (candidatesNeg, r2) = r1.partition{
        case Include(IntersectionType(List(ComplementType(VariableType(_)), _)), EmptyType) => true
        case _ => false
      }
      val newCnstrs = candidates.flatMap{
        case Include(IntersectionType(List(VariableType(v1), s1)), EmptyType) => {
          candidatesNeg.flatMap{
            case Include(IntersectionType(List(ComplementType(VariableType(v2)), s2)), EmptyType) => {
              if(v1 == v2)
                Set(Include(IntersectionType(List(s1, s2)), EmptyType))
              else
                Nil
            }
            case _ => error("")
          }
        }
        case _ => error("")
      }
      newCnstrs ++ system
      */

      def keepOneLevel(s: SetType): SetType = {
        val res = s match {
          case IntersectionType(Seq(EmptyType, _)) => EmptyType
          case IntersectionType(Seq(_, EmptyType)) => EmptyType
          case IntersectionType(Seq(v1, ComplementType(v2))) if v1 == v2 => EmptyType
          case IntersectionType(Seq(ComplementType(v1), v2)) if v1 == v2 => EmptyType
          case IntersectionType(Seq(ConstructorType(_, args))) if args.exists(_ == EmptyType) => EmptyType
          case IntersectionType(Seq(ConstructorType(n1, _), ConstructorType(n2, _))) if n1 != n2 => EmptyType
          case i@IntersectionType(Seq(ConstructorType(n1, args1), ConstructorType(n2, args2))) =>
            if(n1 != n2) 
              error("unexpected")
            else
              keepOneLevel(IntersectionType(Seq(ConstructorType(n1, args1.zip(args2).map{
                case (IntersectionType(lits1), IntersectionType(lits2)) => simplify(IntersectionType(lits1 ++ lits2)) match {
                  case EmptyType => EmptyType
                  case UniversalType => IntersectionType(Seq())
                  case i@IntersectionType(_) => i
                  case v@VariableType(_) => IntersectionType(Seq(v))
                  case v@ComplementType(VariableType(_)) => IntersectionType(Seq(v))
                  case _ => error("unexpected")
                }
                case _ => error("not one level: " + i)
              }))))
          case _ => s
        }
        decreasingOrder(res)
      }

      val trans = system.flatMap[Include, Set[Include]]{
        case Include(EmptyType, EmptyType) => Set()
        case i@Include(IntersectionType(Seq()), EmptyType) => Set()
        case i@Include(IntersectionType(lits), EmptyType) => lits.head match {
          case ConstructorType(_, _) => Set()
          case v@VariableType(_) => system.flatMap[Include, Set[Include]]{
            case Include(IntersectionType(lits2), EmptyType) => {
              if(!lits2.isEmpty && lits2.head == ComplementType(v))
                Set(Include(
                  keepOneLevel(IntersectionType(lits.tail ++ lits2.tail)),
                  EmptyType))
              else Set()
            }
            case _ => Set()
          }
          case ComplementType(v@VariableType(_)) => system.flatMap[Include, Set[Include]]{
            case Include(IntersectionType(lits2), EmptyType) => {
              if(!lits2.isEmpty && lits2.head == v)
                Set(Include(
                  keepOneLevel(IntersectionType(lits.tail ++ lits2.tail)),
                  EmptyType))
              else Set()
            }
            case _ => Set()
          }
          case _ => error("not one level")
        }
        case _ => error("not one level")
      }

      trans ++ system
    }

    def iter(systems: Set[Set[Include]]): Set[Set[Include]] = systems.flatMap(system => {
      val trans = transitiveRule(system)
      val constrSystem = constructorRule(trans)
      val consistentSystems: Set[Set[Include]] = constrSystem.filterNot(sys => sys.exists{
        case Include(UniversalType, EmptyType) => true
        case Include(IntersectionType(Seq(ConstructorType(_, Seq()))), EmptyType) => true
        case _ => false
      })
      val res = consistentSystems.map((system: Set[Include]) => system.flatMap[Include, Set[Include]]{
        case Include(EmptyType, EmptyType) => Set()
        case i => Set(i)
      })
      res
    })

    fix(iter, Set(system))
  }

  def decreasingOrder(s: SetType): SetType = {
    def order(s1: SetType, s2: SetType): Boolean = (s1, s2) match {
      case (VariableType(n1), VariableType(n2)) => n1 > n2
      case (ComplementType(VariableType(n1)), VariableType(n2)) => n1 > n2
      case (VariableType(n1), ComplementType(VariableType(n2))) => n1 > n2
      case (ComplementType(VariableType(n1)), ComplementType(VariableType(n2))) => n1 > n2
      case (VariableType(_), ConstructorType(_, _)) => true
      case (ComplementType(VariableType(_)), ConstructorType(_, _)) => true
      case (ConstructorType(_, _), VariableType(_)) => false
      case (ConstructorType(_, _), ComplementType(VariableType(_))) => false
      case _ => error("not one level")
    }
    val ns = s match {
      case EmptyType => EmptyType
      case IntersectionType(sts) => IntersectionType(sts.sortWith(order))
      case _ => error("not expected")
    }
    ns
  }
  def decreasingOrder(system: Set[Include]): Set[Include] = system.map{
    case Include(s, EmptyType) => Include(decreasingOrder(s), EmptyType)
    case _ => error("not expected")
  }

  def oneLevel(system: Set[Include], constructors: Map[String, Int]): Set[Include] = {

    def canIntersectionLit(lhs: SetType): Option[SetType] = simplify(lhs) match {
      case UniversalType => Some(IntersectionType(Seq()))
      case v@VariableType(_) => Some(IntersectionType(Seq(v)))
      case c@ComplementType(VariableType(_)) => Some(IntersectionType(Seq(c)))
      case i@IntersectionType(sts) if sts.forall(isLiteral) => Some(i)
      case _ => None
    }
    def canOneLevel(lhs: SetType): Option[SetType] = simplify(lhs) match {
      case e@EmptyType => Some(e)
      case UniversalType => Some(IntersectionType(Seq()))
      case v@VariableType(_) => Some(IntersectionType(Seq(v)))
      case c@ComplementType(VariableType(_)) => Some(IntersectionType(Seq(c)))
      case ConstructorType(n, args) => {
        val oneArgs = args.map(canIntersectionLit)
        if(oneArgs.forall(_ != None))
          Some(IntersectionType(Seq(ConstructorType(n, oneArgs.map{_.get}))))
        else
          None
      }
      case i@IntersectionType(sts) => {
        val (constr, rest) = extract(isConstructor _, sts)
        if(!rest.forall(isLiteral))
          None
        else constr match {
          case None => Some(i)
          case Some(c@ConstructorType(_, _)) => {
            canOneLevel(c) match {
              case Some(IntersectionType(Seq(c))) => Some(IntersectionType(rest :+ c))
              case _ => None
            }
          }
          case _ => error("unexpected")
        }
      }
      case _ => None
    }

    def normalForm(lhs: SetType): SetType = lhs match {
      case EmptyType => lhs
      case IntersectionType(sts) => IntersectionType(sts.map{
        case ConstructorType(n, args) => ConstructorType(n, args.map(normalForm))
        case x => x
      })
      case s => IntersectionType(Seq(s))
    }
    def toOneLevels(lhs: SetType): Set[SetType] = {
      import scala.collection.mutable.ListBuffer
      val newCnstrs = ListBuffer[SetType]()
      def toOneLevel0(lhs: SetType): SetType = lhs match {
        case VariableType(_) => lhs
        case IntersectionType(Seq(s)) => s
        case UnionType(Seq(s)) => s
        case _ => {
          val nv = freshVar("x")
          lhs match {
            case EmptyType => newCnstrs += nv
            case UniversalType => newCnstrs += ComplementType(nv)
            case ComplementType(v@VariableType(_)) => newCnstrs += IntersectionType(Seq(nv, v))
            case IntersectionType(sts) => {
              newCnstrs += IntersectionType(ComplementType(nv) +: sts)
              sts.foreach(s => newCnstrs += IntersectionType(Seq(nv, ComplementType(s))))
            }
            case UnionType(sts) => {
              newCnstrs += UnionType(nv +: sts.map(s => ComplementType(s)))
              sts.foreach(s => newCnstrs += IntersectionType(Seq(ComplementType(nv), s)))
            }
            case c@ConstructorType(name, args) => {
              newCnstrs += IntersectionType(Seq(ComplementType(nv), c))
              args.zipWithIndex.foreach{
                case (arg, i) => newCnstrs += IntersectionType(Seq(
                  nv, 
                  ConstructorType(name, args.zipWithIndex.map{case (arg, j) => if(i == j) ComplementType(arg) else UniversalType})))
              }
              constructors.foreach{
                case (n, a) => 
                  if(n != name) 
                    newCnstrs += IntersectionType(Seq(nv, ConstructorType(n, (1 to a).map(_ => UniversalType))))
              }
            }
            case _ => error("unexpected")
          }
          nv
        }
      }
      val nlhs = mapPostorder(lhs, toOneLevel0)
      newCnstrs.toSet + nlhs
    }


    val lhsSystem = system.map{
      case Include(s, EmptyType) => s
      case Include(s1, s2) => IntersectionType(Seq(s1, ComplementType(s2)))
    }
    val res = lhsSystem.flatMap(lhs => canOneLevel(lhs) match {
      case Some(s) => Set(s)
      case None => toOneLevels(lhs)
    })
    val normalRes = res.map(normalForm)
    normalRes.map(lhs => Include(lhs, EmptyType))
  }

  def isConstructor(s: SetType): Boolean = s match {
    case ConstructorType(_, _) => true
    case _ => false
  }
  def isLiteral(s: SetType): Boolean = s match {
    case VariableType(_) => true
    case ComplementType(VariableType(_)) => true
    case _ => false
  }
  def isInterLit(s: SetType): Boolean = s match {
    case IntersectionType(sts) => sts.forall(isLiteral)
    case _ => false
  }
  def isOneLevel(s: SetType): Boolean = s match {
    case EmptyType => true
    case IntersectionType(sts) => {
      val (init, last) = (sts.init, sts.last)
      if(init.forall(isLiteral)) {
        if(isConstructor(last)) {
          val ConstructorType(_, args) = last 
          args.forall(isInterLit)
        } else if(isLiteral(last)) {
          true
        } else false
      } else false
    }
    case _ => false
  }
  def isOneLevel(r: Relation): Boolean = r match {
    case Include(s1, EmptyType) if isOneLevel(s1) => true
    case _ => false
  }
  def isOneLevel(system: Set[Relation]): Boolean = system.forall(isOneLevel)
  def extract[A](p: (A) => Boolean, seq: Seq[A]): (Option[A], Seq[A]) = {
    val (s1, s2) = seq.partition(p)
    if(s1.isEmpty)
      (None, s2)
    else
      (Some(s1.head), s2 ++ s1.tail)
  }
  def extract[A](p: (A) => Boolean, set: Set[A]): (Option[A], Set[A]) = {
    val (s1, s2) = set.partition(p)
    if(s1.isEmpty)
      (None, s2)
    else
      (Some(s1.head), s2 ++ s1.tail)
  }
  def fix[A](f: (A) => A, a: A): A = {
    val na = f(a)
    if(na == a) a else fix(f, na)
  }
  def vars(system: Set[Include]): Set[String] = system.foldLeft(Set[String]())((a, incl) => 
    a ++ Manip.vars(incl))
}
