
import scala.collection.immutable.Set

object Implicit {
  sealed abstract class U 
  case class UInt(i : Int) extends U
  case class UIntSet(s : Set[Int]) extends U
  case class UCons(head : U, tail : U) extends U
  case class UNil() extends U

  def isIntList(u : U) : Boolean = u match {
    case UNil() => true
    case UCons(h, t) => isInt(h) && isIntList(t)
    case _ => false
  }

  def isInt(u : U) : Boolean = u match {
    case UInt(_) => true
    case _ => false
  }
  implicit def fromInt(i : Int) : U = UInt(i)
  implicit def toInt(u : U) : Int = {
    require(isInt(u))
    u match {
      case UInt(i) => i
      //case _ => 0
    }
  }

  def isIntSet(u : U) : Boolean = u match {
    case UIntSet(_) => true
    case _ => false
  }
  implicit def fromIntSet(s : Set[Int]) : U = UIntSet(s)
  implicit def toIntSet(u : U) : Set[Int] = {
    require(isIntSet(u))
    u match {
      case UIntSet(s) => s
      //case _ => Set.empty[Int]
    }
  }

  def sum(u1 : U, u2 : U) : U = {
    require(isInt(u1) && isInt(u2))
    (u1 : Int) + u2
  } 

  def listSize(u : U) : U = {
    require(isIntList(u))

    (u match {
      case UNil() => 0
      case UCons(_, t) => 1 + listSize(t)
    }) : U // weird type hint... alternatively, build a UInt explicitly.

  } ensuring(res => isInt(res) && res >= 0)

  def listContent(u : U) : U = {
    require(isIntList(u))
    u match {
      case UNil() => UIntSet(Set.empty)
      case UCons(h, tail) => UIntSet(listContent(tail) ++ Set[Int](h))
    }
  } ensuring(res => isIntSet(res))
}
