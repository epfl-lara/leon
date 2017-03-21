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

  @production(245)
  @tag("minus")
  def minus(b1: BigInt, b2: BigInt) = b1 - b2

  @production(181)
  @tag("plus")
  def plus(b1: BigInt, b2: BigInt) = b1 + b2
  
  // ???
  //@production(121)
  //def selectorBI(l: List[BigInt]) = l.head

  @production(116)
  @tag("times")
  def times(b1: BigInt, b2: BigInt): BigInt = b1 * b2

  @production(32)
  @tag("div")
  def div(b1: BigInt, b2: BigInt): BigInt = b1 / b2

  @production(18)
  @tag("mod")
  def mod(b1: BigInt, b2: BigInt): BigInt = b1 mod b2

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

  @production(435)
  @tag("not")
  def not(b: Boolean) = !b

  @production(121)
  def or(b1: Boolean, b2: Boolean) = b1 || b2

  /** List [ BigInt ] **/

  @production(209)
  def variableList = variable[List[BigInt]]

  @production(25)
  def nil: List[BigInt] = Nil[BigInt]()

  @production(25)
  def cons(b: BigInt, l: List[BigInt]): List[BigInt] = Cons(b, l)

  /** List ~ polymorphic **/

  @production(209)
  def vLP[Poly] = variable[List[Poly]]

  @production(25)
  def nP[Poly]: List[Poly] = Nil[Poly]()

  @production(25)
  def consP[Poly](h: Poly, t: List[Poly]): List[Poly] = Cons[Poly](h, t)

  /** Polymorphic  */

  @production(1)
  def vp[Poly] = variable[Poly]
  @production(1)
  @tag("equality")
  def eqP[Poly](a: Poly, b: Poly) = a == b
}
