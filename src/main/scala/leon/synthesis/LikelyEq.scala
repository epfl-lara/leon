package leon.synthesis

import leon.Evaluator._
import leon.purescala.Trees._
import leon.purescala.Common._

/*
 * determine if two expressions over arithmetic variables are likely to be the same
 */
object LikelyEq {

  private val min = -5
  private val max = 5

  /*
   * compare e1 and e2, using a list of assignment of integer to the variables in vs
   * Add a default mapping for some set parameters
   */
  def apply(e1: Expr, e2: Expr, vs: Set[Identifier], 
            compare: (Expr, Expr) => Boolean = (e1, e2) => e1 == e2, 
            defaultMap: Map[Identifier, Expr] = Map()): Boolean = {
    var isEq = true
    val vsOrder = vs.toArray
    val counter: Array[Int] = vsOrder.map(_ => min)

    var cont = true
    while(cont && isEq) {
      val m: Map[Identifier, Expr] = vsOrder.zip(counter).map{case (v, c) => (v, IntLiteral(c))}.toMap ++ defaultMap
      val ev1 = eval(m, e1, None)
      val ev2 = eval(m, e2, None)
      (ev1, ev2) match {
        case (OK(v1), OK(v2)) => if(!compare(v1, v2)) isEq = false
        case _ => sys.error("evaluation could not complete")
      }

      var i = 0
      while(i < counter.size && counter(i) >= max)
        i += 1

      if(i == counter.size) {
        cont = false
      } else {
        counter(i) += 1
        if(counter(i) == max) {
          while(i > 0) {
            i -= 1
              counter(i) = min
          }
        }
      }
    }
    isEq
  }

}
