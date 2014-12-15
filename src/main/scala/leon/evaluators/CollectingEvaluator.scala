package leon.evaluators

import scala.collection.immutable.Map
import leon.purescala.Common._
import leon.purescala.Trees._
import leon.purescala.Definitions._
import leon.LeonContext

abstract class CollectingEvaluator(ctx: LeonContext, prog: Program) extends RecursiveEvaluator(ctx, prog, 50000) {
  type RC = DefaultRecContext
  type GC = CollectingGlobalContext
  type ES = Seq[Expr]
  
  def initRC(mappings: Map[Identifier, Expr]) = DefaultRecContext(mappings)
  def initGC = new CollectingGlobalContext()
  
  class CollectingGlobalContext extends GlobalContext {
    var collected : Set[Seq[Expr]] = Set()
    def collect(es : ES) = collected += es
  }
  case class DefaultRecContext(mappings: Map[Identifier, Expr]) extends RecContext {
    def withVars(news: Map[Identifier, Expr]) = copy(news)
  }
  
  // A function that returns a Seq[Expr]
  // This expressions will be evaluated in the current context and then collected in the global environment
  def collecting(e : Expr) : Option[ES]
  
  override def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = {
    for {
      es <- collecting(expr) 
      evaled = es map e
    } gctx.collect(evaled)
    super.e(expr)
  }
  
  def collected : Set[ES] = lastGC map { _.collected } getOrElse Set()
  
}
