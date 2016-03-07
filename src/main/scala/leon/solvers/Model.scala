/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers

import purescala.Expressions._
import purescala.Common.Identifier
import purescala.Quantification.Domains
import purescala.ExprOps._

trait AbstractModel[+This <: Model with AbstractModel[This]]
  extends scala.collection.IterableLike[(Identifier, Expr), This]
  with Printable {

  protected val mapping: Map[Identifier, Expr]

  def set(allVars: Iterable[Identifier]): This = {
    val builder = newBuilder
    builder ++= allVars.map(id => id -> mapping.getOrElse(id, simplestValue(id.getType)))
    builder.result
  }

  def ++(mapping: Map[Identifier, Expr]): This = {
    val builder = newBuilder
    builder ++= this.mapping ++ mapping
    builder.result
  }

  def filter(allVars: Iterable[Identifier]): This = {
    val builder = newBuilder
    for (p <- mapping.filterKeys(allVars.toSet)) {
      builder += p
    }
    builder.result
  }

  def iterator = mapping.iterator
  def seq = mapping.seq

  def asString(implicit ctx: LeonContext) = {
    if (mapping.isEmpty) {
      "Model()"
    } else {
      (for ((k,v) <- mapping.toSeq.sortBy(_._1)) yield {
        val valuePadded = v.asString.replaceAll("\n", "\n"+(" "*26))
        f"  ${k.asString}%-20s -> ${valuePadded}"
      }).mkString("Model(\n", ",\n", "\n)")
    }
  }
}

trait AbstractModelBuilder[+This <: Model with AbstractModel[This]]
  extends scala.collection.mutable.Builder[(Identifier, Expr), This] {

  import scala.collection.mutable.MapBuilder
  protected val mapBuilder = new MapBuilder[Identifier, Expr, Map[Identifier, Expr]](Map.empty)

  def +=(elem: (Identifier, Expr)): this.type = {
    mapBuilder += elem
    this
  }

  def clear(): Unit = mapBuilder.clear
}

class Model(protected val mapping: Map[Identifier, Expr])
  extends AbstractModel[Model]
  with (Identifier => Expr) {

  def newBuilder = new ModelBuilder
  def isDefinedAt(id: Identifier): Boolean = mapping.isDefinedAt(id)
  def get(id: Identifier): Option[Expr] = mapping.get(id)
  def getOrElse[E >: Expr](id: Identifier, e: E): E = get(id).getOrElse(e)
  def ids = mapping.keys
  def apply(id: Identifier): Expr = get(id).getOrElse { throw new IllegalArgumentException }
}

object Model {
  def empty = new Model(Map.empty)
}

class ModelBuilder extends AbstractModelBuilder[Model] {
  def result = new Model(mapBuilder.result)
}

class PartialModel(mapping: Map[Identifier, Expr], val domains: Domains)
  extends Model(mapping)
     with AbstractModel[PartialModel] {

  override def newBuilder = new PartialModelBuilder(domains)
}

object PartialModel {
  def empty = new PartialModel(Map.empty, Domains.empty)
}

class PartialModelBuilder(domains: Domains)
  extends ModelBuilder
     with AbstractModelBuilder[PartialModel] {

  override def result = new PartialModel(mapBuilder.result, domains)
}
