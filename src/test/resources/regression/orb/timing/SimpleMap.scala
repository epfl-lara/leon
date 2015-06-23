import leon.instrumentation._
import leon.invariant._

object SimpleMap {
  sealed abstract class List
  case class Cons(head: (BigInt, BigInt), tail: List) extends List
  case class Nil() extends List

  def size(l : List) : BigInt = (l match {
    case Cons(_, xs) => 1 + size(xs)
    case _ => 0
  })

  def insert(l: List, key: BigInt, value: BigInt): List = {
    Cons((key, value), l)
  } ensuring(res => tmpl((a) => time <= a))

  def getOrElse(l: List, key: BigInt, elseValue: BigInt): BigInt = {
    l match {
      case Nil() => elseValue
      case Cons((currKey, currValue), _) if (currKey == key) => currValue
      case Cons(_, tail) => getOrElse(tail, key, elseValue)
    }
  } ensuring(res => tmpl((a, b) => time <= a*size(l) + b))
}