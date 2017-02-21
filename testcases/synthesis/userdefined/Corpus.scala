package leon
package grammar

import leon.lang._
import leon.lang.synthesis._
import leon.collection._
import annotation.grammar._


object Grammar {

  // BIGINT
  @production(2306)
  def vr = variable[BigInt]

  @production(500)
  @tag("0")
  def zero = BigInt(0)

  @production(500)
  @tag("1")
  def one = BigInt(1)
/*
  @production(100)
  def pairOneBI(p: (BigInt, BigInt)): BigInt = p._1

  @production(100)
  def pairTwoBI(p: (BigInt, BigInt)): BigInt = p._1

  @production(30)
  def tripOneBI(p: (BigInt, BigInt, BigInt)): BigInt = p._1

  @production(30)
  def tripTwoBI(p: (BigInt, BigInt, BigInt)): BigInt = p._2
  
  @production(30)
  def tripThreeBI(p: (BigInt, BigInt, BigInt)): BigInt = p._3
*/
  @production(245)
  @tag("minus")
  def minus(b1: BigInt, b2: BigInt) = b1 - b2

  @production(181)
  @tag("plus")
  def plus(b1: BigInt, b2: BigInt) = b1 + b2
  
  // ???
  //@production(121)
  //def selectorBI(l: List[BigInt]) = l.head

/*
  @production(116)
  @tag("times")
  def times(b1: BigInt, b2: BigInt): BigInt = b1 * b2
*/
  @production(46)
  @tag("ite")
  def iteBI(cond: Boolean, thenn: BigInt, elze: BigInt) = {
    if(cond) thenn else elze
  }
/*
  @production(32)
  @tag("div")
  def div(b1: BigInt, b2: BigInt): BigInt = b1 / b2

  @production(18)
  @tag("mod")
  def mod(b1: BigInt, b2: BigInt): BigInt = b1 mod b2
*/

  // BOOLEAN
  @production(1533)
  @tag("equality")
  def equalsBool(b1: Boolean, b2: Boolean) = b1 == b2


  @production(956)
  def varBool = variable[Boolean]
  
  //@production(883)
  //@tag("and")
  //def and(b1: Boolean, b2: Boolean) = b1 && b2

  @production(250)
  @tag("booleanC")
  def t = true

  @production(250)
  @tag("booleanC")
  def f = false

  @production(900)
  def ge(b1: BigInt, b2: BigInt) = b1 >= b2

  @production(600)
  def gt(b1: BigInt, b2: BigInt) = b1 > b2
/*
  @production(435)
  @tag("not")
  def not(b: Boolean) = !b

  @production(229)
  @tag("ite")
  def iteBool(c: Boolean, t: Boolean, e: Boolean) =
    if (c) t else e

  @production(100)
  def pairOneB(p: (Boolean, Boolean)): Boolean = p._1

  @production(100)
  def pairTwoB(p: (Boolean, Boolean)): Boolean = p._1

  @production(30)
  def tripOneB(p: (Boolean, Boolean, Boolean)): Boolean = p._1

  @production(30)
  def tripTwoB(p: (Boolean, Boolean, Boolean)): Boolean = p._2
  
  @production(30)
  def tripThreeB(p: (Boolean, Boolean, Boolean)): Boolean = p._3

  @production(121)
  def or(b1: Boolean, b2: Boolean) = b1 || b2

  @production(65)
  def isInstOfCons(l: List[BigInt]) = l.isInstanceOf[Cons[BigInt]]

  @production(65)
  def isInstOfNil(l: List[BigInt]) = l.isInstanceOf[Nil[BigInt]]

  @production(41)
  def implies(b1: Boolean, b2: Boolean) = b1 ==> b2
*/
  /** List **/

  @production(209)
  def variableList = variable[List[BigInt]]

  @production(25)
  def nil: List[BigInt] = Nil[BigInt]()

  @production(25)
  def cons(b: BigInt, l: List[BigInt]): List[BigInt] = Cons(b, l)

}
