/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars
package aspects

import purescala.Expressions.Expr

/**
 * Persistant aspects allow label information to be propagated down:
 * Int{e} means (Int with a terminal 'e'). And thus, the Closure grammar
 * is able to have, as production:
 *   Int=>Int  :=  (e: Int) => Int{e}
 * In turn, all Int productions, e.g. Int := Int + Int, gets transformed by the
 * aspect and generate:
 *   Int{e}  :=  Int{e} + Int{e}
 *
 * This with the ExtraTerminals grammar, enables the generation of expressions
 * like:
 *   e + 1
 */
abstract class PersistantAspect extends Aspect {
  def applyTo(lab: Label, ps: Seq[ProductionRule[Label, Expr]])(implicit ctx: LeonContext) = {
    ps.map { p =>
      p.copy(subTrees = p.subTrees.map(lab => lab.withAspect(this)))
    }
  }
}
