/* Copyright 2009-2016 EPFL, Lausanne */

package leon.theories
import leon.annotation._

@library
sealed abstract class String {
  def size: BigInt = (this match {
    case StringCons(_, tail) => 1 + tail.size
    case StringNil() => BigInt(0)
  }) ensuring (_ >= 0)

  def concat(that: String): String = this match {
    case StringCons(head, tail) => StringCons(head, tail concat that)
    case StringNil() => that
  }

  def take(i: BigInt): String = this match {
    case StringCons(head, tail) if i > 0 => StringCons(head, tail take (i - 1))
    case _ => StringNil()
  }

  def drop(i: BigInt): String = this match {
    case StringCons(head, tail) if i > 0 => tail drop (i - 1)
    case _ => this
  }

  def slice(from: BigInt, to: BigInt): String = drop(from).take(to - from)
}

case class StringCons(head: Char, tail: String) extends String
case class StringNil() extends String
