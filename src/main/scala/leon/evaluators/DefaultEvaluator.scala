/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package evaluators

import purescala.Definitions.Program

class DefaultEvaluator(ctx: LeonContext, prog: Program)
  extends RecursiveEvaluator(ctx, prog, 50000)
  with HasDefaultGlobalContext
  with HasDefaultRecContext
