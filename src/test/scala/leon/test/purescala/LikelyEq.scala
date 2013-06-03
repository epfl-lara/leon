/* Copyright 2009-2013 EPFL, Lausanne */

package leon.test.purescala

import leon._
import leon.evaluators._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.TreeOps.replace
import leon.purescala.Trees._

/*
 * Determine if two expressions over arithmetic variables are likely to be equal.
 *
 * This is a probabilistic based approach, it does not rely on any external solver and can
 * only prove the non equality of two expressions.
 */
object LikelyEq {
  private lazy val evaluator : Evaluator = new DefaultEvaluator(LeonContext(reporter = new SilentReporter), Program.empty)

  private val min = -5
  private val max = 5

  /*
   * compare e1 and e2, using a list of assignment of integer to the variables in vs.
   * Pre is a boolean expression precondition over the same variables that must be evaluated to true
   * before testing equality.
   * Add a default mapping for some set parameters
   * Note that the default map could contain a mapping for variables to other parameters
   * It is thus necessary to first select values for those parameters and then substitute
   * into the default map !
   */
  def apply(e1: Expr, e2: Expr, vs: Set[Identifier], pre: Expr = BooleanLiteral(true),
            compare: (Expr, Expr) => Boolean = (e1, e2) => e1 == e2, 
            defaultMap: Map[Identifier, Expr] = Map()): Boolean = {
    if(vs.isEmpty) {
      val ndm = defaultMap.map { case (id, expr) => (id, evaluator.eval(expr).asInstanceOf[EvaluationResults.Successful].value) } //TODO: not quite sure why I need to do this...
      (evaluator.eval(e1, ndm), evaluator.eval(e2, defaultMap)) match {
        case (EvaluationResults.Successful(v1), EvaluationResults.Successful(v2)) => compare(v1, v2)
        case (err1, err2) => sys.error("evaluation could not complete, got: (" + err1 + ", " + err2 + ")")
      }
    } else {
      var isEq = true
      val vsOrder = vs.toArray
      val counters: Array[Int] = vsOrder.map(_ => min)
      var i = 0

      var cont = true
      while(i < counters.size && isEq) {
        val m: Map[Expr, Expr] = vsOrder.zip(counters).map{case (v, c) => (Variable(v), IntLiteral(c))}.toMap
        val ne1 = replace(m, e1)
        val ne2 = replace(m, e2)
        val npre = replace(m, pre)
        val ndm = defaultMap.map{ case (id, expr) => (id, evaluator.eval(expr, m.map{case (Variable(id), t) => (id, t)}).asInstanceOf[EvaluationResults.Successful].value) }
        evaluator.eval(npre, ndm) match {
          case EvaluationResults.Successful(BooleanLiteral(false)) =>
          case EvaluationResults.Successful(BooleanLiteral(true)) =>
            val ev1 = evaluator.eval(ne1, ndm)
            val ev2 = evaluator.eval(ne2, ndm)
            (ev1, ev2) match {
              case (EvaluationResults.Successful(v1), EvaluationResults.Successful(v2)) => if(!compare(v1, v2)) isEq = false
              case (err1, err2) => sys.error("evaluation could not complete, got: (" + err1 + ", " + err2 + ")")
            }
          case err => sys.error("evaluation of precondition could not complete, got: " + err)
        }

        if(counters(i) < max)
          counters(i) += 1
        else {
          while(i < counters.size && counters(i) >= max) {
            counters(i) = min
            i += 1
          }
          if(i < counters.size) {
            counters(i) += 1
            i = 0
          }
        }
      }
      isEq
    }
  }

}
