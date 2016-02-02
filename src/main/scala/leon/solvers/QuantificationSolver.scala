package leon
package solvers

import purescala.Common._
import purescala.Expressions._
import purescala.Quantification._
import purescala.Definitions._
import purescala.Types._

class HenkinModel(mapping: Map[Identifier, Expr], val doms: HenkinDomains)
  extends Model(mapping)
     with AbstractModel[HenkinModel] {
  override def newBuilder = new HenkinModelBuilder(doms)

  def domain(expr: Expr) = doms.get(expr)
}

object HenkinModel {
  def empty = new HenkinModel(Map.empty, HenkinDomains.empty)
}

class HenkinModelBuilder(domains: HenkinDomains)
  extends ModelBuilder
     with AbstractModelBuilder[HenkinModel] {
  override def result = new HenkinModel(mapBuilder.result, domains)
}

trait QuantificationSolver extends Solver {
  val program: Program

  protected lazy val requireQuantification = program.definedFunctions.exists { fd =>
    purescala.ExprOps.exists { case _: Forall => true case _ => false } (fd.fullBody)
  }
}
