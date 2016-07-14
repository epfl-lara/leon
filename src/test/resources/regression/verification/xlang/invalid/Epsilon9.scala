/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.lang.xlang._

object Epsilon9 {

  def random(): BigInt = epsilon((x: BigInt) => true)

  /*
   * The implementation relies on a potential bug in random(), when
   * two calls of random with the same args (0 here) will return
   * the same value. If that's the case, then we can prove the
   * postcondition. Epsilon should behave really randomly, so that
   * postcondition should be invalid.
   */
  def findPositive(): BigInt = {
    val x = random()
    if(x < 0) {
      -random()
    } else {
      x
    }
  } ensuring(res => res >= 0)

}
