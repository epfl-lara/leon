package leon
package solvers

import purescala.Common._
import purescala.Expressions._
import purescala.Quantification._
import purescala.Types._

class HenkinModel(mapping: Map[Identifier, Expr], doms: HenkinDomains)
  extends Model(mapping)
     with AbstractModel[HenkinModel] {
  override def newBuilder = new HenkinModelBuilder(doms)

  def domains: Map[TypeTree, Set[Seq[Expr]]] = doms.domains
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

trait QuantificationSolver {
  def getModel: HenkinModel
}
