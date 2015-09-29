/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers

import utils.{DebugSectionSolver, Interruptible}
import purescala.Expressions._
import purescala.Common.{Tree, Identifier}
import purescala.ExprOps._
import verification.VC

trait AbstractModel[+This <: Model with AbstractModel[This]]
  extends scala.collection.IterableLike[(Identifier, Expr), This] {

  protected val mapping: Map[Identifier, Expr]

  def fill(allVars: Iterable[Identifier]): This = {
    val builder = newBuilder
    builder ++= mapping ++ (allVars.toSet -- mapping.keys).map(id => id -> simplestValue(id.getType))
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
        f"  ${k.asString}%-20s -> ${v.asString}"
      }).mkString("Model(\n", ",\n", ")")
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
  def apply(id: Identifier): Expr = get(id).getOrElse { throw new IllegalArgumentException }
}

object Model {
  def empty = new Model(Map.empty)
}

class ModelBuilder extends AbstractModelBuilder[Model] {
  def result = new Model(mapBuilder.result)
}

trait Solver extends Interruptible {
  def name: String
  val context: LeonContext

  implicit lazy val leonContext = context

  def assertCnstr(expression: Expr): Unit
  def assertVC(vc: VC) = {
    assertCnstr(Not(vc.condition))
  }

  def check: Option[Boolean]
  def getModel: Model
  def getResultSolver: Option[Solver] = Some(this)

  def free()

  def reset()

  def push(): Unit
  def pop(): Unit

  def checkAssumptions(assumptions: Set[Expr]): Option[Boolean]
  def getUnsatCore: Set[Expr]

  protected def unsupported(t: Tree): Nothing = {
    val err = SolverUnsupportedError(t, this, None)
    leonContext.reporter.warning(err.getMessage)
    throw err
  }

  protected def unsupported(t: Tree, str: String): Nothing = {
    val err = SolverUnsupportedError(t, this, Some(str))
    leonContext.reporter.warning(err.getMessage)
    throw err
  }

  implicit val debugSection = DebugSectionSolver

  private[solvers] def debugS(msg: String) = {
    context.reporter.debug("["+name+"] "+msg)
  }
}
