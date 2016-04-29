/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package evaluators

import purescala.Definitions.Program

class DefaultEvaluator(ctx: LeonContext, prog: Program, bank: EvaluationBank = new EvaluationBank)
  extends RecursiveEvaluator(ctx, prog, bank, 50000)
     with HasDefaultGlobalContext
     with HasDefaultRecContext
