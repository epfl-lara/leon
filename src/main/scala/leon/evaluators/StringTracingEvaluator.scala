/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package evaluators

import purescala.Extractors.Operator
import purescala.Expressions._
import purescala.Definitions.Program
import purescala.Expressions.Expr

class StringTracingEvaluator(ctx: LeonContext, prog: Program) extends ContextualEvaluator(ctx, prog, 50000) with DefaultContexts {

  val underlying = new DefaultEvaluator(ctx, prog)
  override type Value = (Expr, Expr)

  override val description: String = ??? // FIXME
  override val name: String = ??? // FIXME

  protected def e(expr: Expr)(implicit rctx: RC, gctx: GC): (Expr, Expr) = expr match {
    case StringConcat(s1, s2) =>
      val (es1, t1) = e(s1)
      val (es2, t2) = e(s2)
      (underlying.e(StringConcat(es1, es2)), StringConcat(t1, t2))

    case StringLength(_) => ??? // FIXME
    case StringLiteral(_) => ??? // FIXME

    case Operator(es, builder) =>
      val (ees, ts) = es.map(e).unzip
      (underlying.e(builder(ees)), builder(ts))
  }


}
