package leon
package invariant.util

import purescala.ExprOps._
import purescala.Expressions._
import purescala.Extractors.Operator
import purescala.Types.{ClassType, TypeParameter}

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
      case (Operator(args1, _), Operator(args2, _)) =>        
        opEquals(e1, e2) && (args1.size == args2.size) && (args1 zip args2).forall {
          case (a1, a2) => structurallyEqual(a1, a2)
        }
      case _ =>
        false
    }
  }
  
  def opEquals(e1: Expr, e2: Expr): Boolean = {
    (e1, e2) match {
      case (FunctionInvocation(tfd1, _), FunctionInvocation(tfd2, _)) 
        if tfd1.fd == tfd2.fd => true
      case (CaseClass(cct1, _), CaseClass(cct2, _)) 
        if cct1.classDef == cct2.classDef => true
      case (CaseClassSelector(cct1, _, fld1), CaseClassSelector(cct2, _, fld2))
        if cct1.classDef == cct2.classDef && fld1 == fld2 => true  
      case _ if e1.getClass.equals(e2.getClass) => true  // check if e1 and e2 are same instances of the same class        
      case _ if e1.isInstanceOf[MethodInvocation] || e2.isInstanceOf[MethodInvocation] =>
        throw new IllegalArgumentException("MethodInvocations are not supported")
      case _ =>
        //println(s"Not op equal: ($e1,$e2) classes: (${e1.getClass}, ${e2.getClass})")
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

  val hashcode = {
    var opndcount = 0 // operand count
    var opcount = 0 // operator count
    postTraversal {
      case t: Terminal => opndcount += 1
      case _           => opcount += 1
    }(e)
    (opndcount << 16) ^ opcount
  }
  
  override def hashCode = hashcode
}