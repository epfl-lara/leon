/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers

import leon.utils.{DebugSectionSolver, Interruptible}
import purescala.Expressions._
import purescala.Common.Tree
import verification.VC

trait AbstractModel[+This <: Model with AbstractModel[This]]
  extends scala.collection.IterableLike[(Identifier, Expr), This] {

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

  def asString(ctx: LeonContext): String = {
    val strings = toSeq.sortBy(_._1.name).map {
      case (id, v) => (id.asString(ctx), purescala.PrettyPrinter(v))
    }

    if (strings.nonEmpty) {
      val max = strings.map(_._1.length).max

      strings.map { case (id, v) => ("%-"+max+"s -> %s").format(id, v) }.mkString("\n")
    } else {
      "(Empty model)"
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

  // This is ugly, but helpful for smtlib solvers
  def dbg(msg: => Any) {}

  def assertCnstr(expression: Expr): Unit
  def assertVC(vc: VC) = {
    dbg(s"; Solving $vc @ ${vc.getPos}\n")
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
