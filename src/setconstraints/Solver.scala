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

  def cascadingSystems(system: Set[Include], constructors: Map[String, Int]): Set[Set[Include]] = {

    def constructorRule(system: Set[Include]): Set[Set[Include]] = {
      val (option, rest) = extract((x: Include) => x match {
        case Include(ConstructorType(_, args), EmptyType) => true 
        case _ => false
      }, system)
      option match {
        case Some(Include(ConstructorType(_, args), EmptyType)) =>
          args.map(arg => rest + Include(arg, EmptyType)).toSet
        case _ => error("no constructor found to apply rule")
      }
    }

    def transitiveRule(system: Set[Include]): Set[Include] = {
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
    }

    import scala.collection.mutable.{Set => MSet}

    def findS0(s: MSet[Set[Include]]): Option[(Set[Include], (Include, Include))] = {
      null
    }
    val systems = MSet[Set[Include]]()
    while(!systems.isEmpty) {

    }

    null
  }

  def decreasingOrder(system: Set[Include]): Set[Include] = {
    def order(s1: SetType, s2: SetType): Boolean = (s1, s2) match {
      case (VariableType(n1), VariableType(n2)) => n1 > n2
      case (VariableType(_), ConstructorType(_, _)) => true
      case (ConstructorType(_, _), VariableType(_)) => false
      case _ => error("not one level")
    }
    system.map{
      case Include(s, EmptyType) => {
        val ns = s match {
          case EmptyType => EmptyType
          case IntersectionType(sts) => IntersectionType(sts.sortWith(order))
          case _ => error("not expected")
        }
        Include(ns, EmptyType)
      }
      case _ => error("not expected")
    }

  }

  def oneLevel(system: Set[Include], constructors: Map[String, Int]): Set[Include] = {

    def toOneLevels(lhs: SetType): Set[SetType] = {
      import scala.collection.mutable.ListBuffer
      val newCnstrs = ListBuffer[SetType]()
      def toOneLevel0(lhs: SetType): SetType = lhs match {
        case VariableType(_) => lhs
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

    def normalForm(lhs: SetType): SetType = lhs match {
      case EmptyType => lhs
      case IntersectionType(sts) => IntersectionType(sts.map{
        case ConstructorType(n, args) => ConstructorType(n, args.map(normalForm))
        case x => x
      })
      case s => IntersectionType(Seq(s))
    }

    val lhsSystem = system.map{
      case Include(s, EmptyType) => s
      case Include(s1, s2) => IntersectionType(Seq(s1, ComplementType(s2)))
    }
    val (oneLev, notOneLev) = lhsSystem.partition(isOneLevel)
    val res = notOneLev.flatMap(lhs => toOneLevels(lhs))
    val normalRes = (res ++ oneLev).map(normalForm)
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
  /*
  def isConjunctionLit(s: SetType): Boolean = s match {
    case IntersectionType(sts) if sts.foldLeft(true)((b, st) => b && isLiteral(st) && sts.forall(l => l != ComplementType(st))) => false
    case _ => false
  }
  def isConjunctionLitWithUniversal(s: SetType): Boolean = flatten(s) match {
    case IntersectionType(sts) if sts.last == UniversalType && isConjunctionLit(IntersectionType(sts.init)) => true
    case _ => false
  }
  */
  def extract[A](p: (A) => Boolean, set: Set[A]): (Option[A], Set[A]) = {
    val (s1, s2) = set.partition(p)
    if(s1.isEmpty)
      (None, s2)
    else
      (Some(s1.head), s2 ++ s1.tail)
  }
}
