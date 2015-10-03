package leon
package invariant.util

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import scala.collection.mutable.{ Set => MutableSet, Map => MutableMap }

/**
 * A class that looks for structural equality of expressions
 * by ignoring the variable names.
 * Useful for factoring common parts of two expressions into functions.
 */
class ExprStructure(val e: Expr) {
  def structurallyEqual(e1: Expr, e2: Expr): Boolean = {
    (e1, e2) match {
      case (t1: Terminal, t2: Terminal) =>
        // we need to specially handle type parameters as they are not considered equal by default
        (t1.getType, t2.getType) match {
          case (ct1: ClassType, ct2: ClassType) =>
            if (ct1.classDef == ct2.classDef && ct1.tps.size == ct2.tps.size) {
              (ct1.tps zip ct2.tps).forall {
                case (TypeParameter(_), TypeParameter(_)) =>
                  true
                case (a, b) =>
                  println(s"Checking Type arguments: $a, $b")
                  a == b
              }
            } else false
          case (ty1, ty2) => ty1 == ty2
        }
      case (Operator(args1, op1), Operator(args2, op2)) =>
        (op1 == op2) && (args1.size == args2.size) && (args1 zip args2).forall {
          case (a1, a2) => structurallyEqual(a1, a2)
        }
      case _ =>
        false
    }
  }

  override def equals(other: Any) = {
    other match {
      case other: ExprStructure =>
        structurallyEqual(e, other.e)
      case _ =>
        false
    }
  }

  override def hashCode = {
    var opndcount = 0 // operand count
    var opcount = 0 // operator count
    postTraversal {
      case t: Terminal => opndcount += 1
      case _ => opcount += 1
    }(e)
    (opndcount << 16) ^ opcount
  }
}