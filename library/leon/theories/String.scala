/* Copyright 2009-2016 EPFL, Lausanne */

package leon.theories
import leon.annotation._

@library
sealed abstract class String {
  def size: BigInt = (this match {
    case StringCons(_, tail) => 1 + tail.size
    case StringNil() => BigInt(0)
  }) ensuring (_ >= 0)
  
  def sizeI: Int = this match {
    case StringCons(_, tail) => 1 + tail.sizeI
    case StringNil() => 0
  }

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
  
  @isabelle.noBody()
  def takeI(i: Int): String = this match {
    case StringCons(head, tail) if i > 0 => StringCons(head, tail takeI (i - 1))
    case _ => StringNil()
  }

  @isabelle.noBody()
  def dropI(i: Int): String = this match {
    case StringCons(head, tail) if i > 0 => tail dropI (i - 1)
    case _ => this
  }

  def slice(from: BigInt, to: BigInt): String = drop(from).take(to - from)
  def sliceI(from: Int, to: Int): String = dropI(from).takeI(to - from)
}

case class StringCons(head: Char, tail: String) extends String
case class StringNil() extends String

@library
object String {
  def fromChar(i: Char): String = {
    StringCons(i, StringNil())
  }

  @isabelle.noBody()
  def fromBigInt(i: BigInt): String =
    if(i < 0) StringCons('-', fromBigInt(-i))
    else if(i == BigInt(0)) StringCons('0', StringNil())
    else if(i == BigInt(1)) StringCons('1', StringNil())
    else if(i == BigInt(2)) StringCons('2', StringNil())
    else if(i == BigInt(3)) StringCons('3', StringNil())
    else if(i == BigInt(4)) StringCons('4', StringNil())
    else if(i == BigInt(5)) StringCons('5', StringNil())
    else if(i == BigInt(6)) StringCons('6', StringNil())
    else if(i == BigInt(7)) StringCons('7', StringNil())
    else if(i == BigInt(8)) StringCons('8', StringNil())
    else if(i == BigInt(9)) StringCons('9', StringNil())   
    else fromBigInt(i / 10).concat(fromBigInt(i % 10))

  @isabelle.noBody()
  def fromInt(i: Int): String = i match {
    case -2147483648 => StringCons('-', StringCons('2', fromInt(147483648)))
    case i  if i < 0 => StringCons('-', fromInt(-i))
    case 0 => StringCons('0', StringNil())
    case 1 => StringCons('1', StringNil())
    case 2 => StringCons('2', StringNil())
    case 3 => StringCons('3', StringNil())
    case 4 => StringCons('4', StringNil())
    case 5 => StringCons('5', StringNil())
    case 6 => StringCons('6', StringNil())
    case 7 => StringCons('7', StringNil())
    case 8 => StringCons('8', StringNil())
    case 9 => StringCons('9', StringNil())
    case i => fromInt(i / 10).concat(fromInt(i % 10))
  }
  
  def fromBoolean(b: Boolean): String = {
    if(b) StringCons('t', StringCons('r', StringCons('u', StringCons('e', StringNil()))))
    else StringCons('f', StringCons('a', StringCons('l', StringCons('s', StringCons('e', StringNil())))))
  }
}
