package leon
package evaluators

import purescala.Definitions.Program

class DefaultEvaluator(ctx: LeonContext, prog: Program)
  extends RecursiveEvaluator(ctx, prog, 5000)
  with DefaultContexts