package setconstraints

import Trees._
import Manip._

object Solver {

  def apply(system: List[Relation]): Option[List[FixPoint]] = {
    error("TODO")
  }

  def solve(system: List[Relation]): Option[List[Equals]] = {
    error("TODO")
  }

  def extract[A](p: (A) => Boolean, list: List[A]): (Option[A], List[A]) = list match {
    case Nil => (None, Nil)
    case x::xs => if(p(x)) (Some(x), xs) else {
      val (c1, c2) = extract(p, xs)
      (c1, x :: c2)
    }
  }

  def cascadingSystems(system: List[Include]): List[List[Include]] = {

    def constructorRule(system: List[Include]): List[List[Include]] = {
      val (option, rest) = extract((x: Include) => x match {
        case Include(ConstructorType(_, args), EmptyType) => true 
        case _ => false
      }, system)
      option match {
        case Some(Include(ConstructorType(_, args), EmptyType)) =>
          args.map(arg => Include(arg, EmptyType) :: rest).toList
        case None => error("no constructor found to apply rule")
      }
    /*
      system.zipWithIndex.map{
        case (Include(ConstructorType(_, args), EmptyType), i) => {
          val (r1, _::r2) = system.splitAt(i)
          val rest = r1 ::: r2
          args.map(arg => Include(arg, EmptyType) :: rest).toList
        }
        case (incl, _) => List(incl)
      }
      */
    }

/*
    def transitiveRule(system: List[Include]): List[Include] = {
      val (candidates, rest) = system.partition{
        case Include(IntersectionType(List(VariableType(_), _)), EmptyType) => true
        case _ => false
      }
      candidates.flatMap{
        case Include(IntersectionType(List(VariableType(v1), s1)), EmptyType) => {
          candidates.flatMap{
            case Include(IntersectionType(List(ComplementType(VariableType(v2)), s2)), EmptyType) => {
              if(v1 == v2)
                List(
            }
          }
        }
      }
      null
    }
    */

    null
  }

  def oneLevel(system: List[Include]): List[Include] = {

    val constructors: List[(String, Int)] = null

    def toOneLevels(incl: Include): List[Include] = {
      import scala.collection.mutable.ListBuffer
      val newCnstrs = ListBuffer[Include]()
      def toOneLevel0(lhs: SetType): SetType = {
        val nv = freshVar("x")
        lhs match {
          case EmptyType => newCnstrs += Include(nv, EmptyType)
          case UniversalType => newCnstrs += Include(ComplementType(nv), EmptyType)
          case ComplementType(v@VariableType(_)) => newCnstrs += Include(IntersectionType(List(nv, v)), EmptyType)
          case IntersectionType(sts) => {
            newCnstrs += Include(IntersectionType(ComplementType(nv) +: sts), EmptyType)
            sts.foreach(s => newCnstrs += Include(IntersectionType(List(nv, ComplementType(s))), EmptyType))
          }
          case UnionType(sts) => {
            newCnstrs += Include(UnionType(nv +: sts.map(s => ComplementType(s))), EmptyType)
            sts.foreach(s => newCnstrs += Include(IntersectionType(List(ComplementType(nv), s)), EmptyType))
          }
          case c@ConstructorType(name, args) => {
            newCnstrs += Include(IntersectionType(List(ComplementType(nv), c)), EmptyType)
            args.zipWithIndex.foreach{case (arg, i) => newCnstrs += Include(IntersectionType(List(
              nv, ConstructorType(name, args.zipWithIndex.map{case (arg, j) => if(i == j) ComplementType(arg) else UniversalType}))), EmptyType)}
            constructors.foreach{case (n, a) => if(n != name) newCnstrs += Include(IntersectionType(List(nv, ConstructorType(n, (1 to a).map(_ => UniversalType)))), EmptyType)}
          }
          case _ => error("unexpected")
        }
        nv
      }
      val Include(lhs, EmptyType) = incl
      val nlhs = map(lhs, toOneLevel0) 
      Include(nlhs, EmptyType) :: newCnstrs.toList
    }
/*
    def oneLevelIter(system: List[Include], oneLeveled: List[Include]): List[Include] = system match {
      case Nil => oneLeveled
      case (i::is) => {
        val (ni, nis) = toOneLevel(i)
        oneLevelIter(nis ::: is, ni :: oneLeveled)
      }
    }
    */

    val emptyRightSystem = system.map{
      case Include(s1, s2) if s2 != EmptyType => Include(IntersectionType(List(s1, ComplementType(s2))), EmptyType)
      case incl => incl
    }
    val (oneLev, notOneLev) = emptyRightSystem.partition(isOneLevel)
    val res = notOneLev.flatMap(incl => toOneLevels(incl))
    res ::: oneLev
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
  def isConjunctionLit(s: SetType): Boolean = flatten(s) match {
    case IntersectionType(sts) if sts.foldLeft(true)((b, st) => b && isLiteral(st) && sts.forall(l => l != ComplementType(st))) => false
    case _ => false
  }
  def isConjunctionLitWithUniversal(s: SetType): Boolean = flatten(s) match {
    case IntersectionType(sts) if sts.last == UniversalType && isConjunctionLit(IntersectionType(sts.init)) => true
    case _ => false
  }
  def isOneLevel(s: SetType): Boolean = flatten(s) match {
    case EmptyType => true
    case IntersectionType(sts) if isConstructor(sts.last) && isConjunctionLit(IntersectionType(sts.init)) => {
      val ConstructorType(_, args) = sts.last 
      args.forall(isConjunctionLitWithUniversal)
    }
    case s => isConjunctionLitWithUniversal(s)
  }
  def isOneLevel(r: Relation): Boolean = r match {
    case Include(s1, EmptyType) if isOneLevel(s1) => true
    case _ => false
  }
  def isOneLevel(system: List[Relation]): Boolean = system.forall(isOneLevel)
}
