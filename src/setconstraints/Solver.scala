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

  def oneLevel(system: List[Include]): List[Include] = {

    val emptyRightSystem = system.map{
      case Include(s1, s2) if s2 != EmptyType => Include(IntersectionType(List(s1, ComplementType(s2))), EmptyType)
      case incl => incl
    }


    error("TODO")
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
