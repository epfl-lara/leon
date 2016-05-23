/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers

import purescala.Types._
import purescala.Common._

case class DataType(sym: Identifier, cases: Seq[Constructor]) extends Printable {
  def asString(implicit ctx: LeonContext) = {
    "Datatype: "+sym.asString+"\n"+cases.map(c => " - "+c.asString(ctx)).mkString("\n")
  }
}
case class Constructor(sym: Identifier, tpe: TypeTree, fields: Seq[(Identifier, TypeTree)]) extends Printable {
  def asString(implicit ctx: LeonContext) = {
    sym.asString(ctx)+" ["+tpe.asString(ctx)+"] "+fields.map(f => f._1.asString(ctx)+": "+f._2.asString(ctx)).mkString("(", ", ", ")")
  }
}

class ADTManager(ctx: LeonContext) {
  val reporter = ctx.reporter

  protected def freshId(id: Identifier): Identifier = freshId(id.name)
  protected def freshId(name: String): Identifier = FreshIdentifier(name)

  protected def getHierarchy(ct: ClassType): (ClassType, Seq[CaseClassType]) = ct.parent match {
    case Some(p) =>
      getHierarchy(p)
    case None => (ct, ct match {
      case act: AbstractClassType =>
        act.knownCCDescendants
      case cct: CaseClassType =>
        List(cct)
    })
  }

  protected var defined = Set[TypeTree]()
  protected var locked  = Set[TypeTree]()

  protected var discovered = Map[TypeTree, DataType]()

  def defineADT(t: TypeTree): Either[Map[TypeTree, DataType], Set[TypeTree]] = {
    discovered = Map()
    locked     = Set()

    findDependencies(t)

    val conflicts = discovered.keySet & locked

    if (conflicts(t)) {
      // There is no way to solve this, the type we requested is in conflict
      val str = "Encountered ADT that can't be defined.\n" +
        "It appears it has recursive references through non-structural types (such as arrays, maps, or sets)."
      val err = new Unsupported(t, str)(ctx)
      reporter.warning(err.getMessage)
      throw err
    } else {
      // We might be able to define some despite conflicts
      if (conflicts.isEmpty) {
        for ((t, dt) <- discovered) {
          defined += t
        }
        Left(discovered)
      } else {
        Right(conflicts)
      }
    }
  }

  def forEachType(t: TypeTree)(f: TypeTree => Unit): Unit = t match {
    case NAryType(tps, builder) =>
      f(t)
      // note: each of the tps could be abstract classes in which case we need to
      // lock their dependencies, transitively.
      tps.foreach {
        case ct: ClassType =>
          val (root, sub) = getHierarchy(ct)
          (root +: sub).flatMap(_.fields.map(_.getType)).foreach(subt => forEachType(subt)(f))
        case othert =>
          forEachType(othert)(f)
      }
  }

  protected def findDependencies(t: TypeTree): Unit = t match {
    case _: SetType | _: MapType =>
      forEachType(t) { tpe =>
        if (!defined(tpe)) {
          locked += tpe
        }
      }

    case ct: ClassType =>
      val (root, sub) = getHierarchy(ct)

      if (!(discovered contains root) && !(defined contains root)) {
        val sym = freshId(root.id)

        val conss = sub.map { case cct =>
          Constructor(freshId(cct.id), cct, cct.fields.map(vd => (freshId(vd.id), vd.getType)))
        }

        discovered += (root -> DataType(sym, conss))

        // look for dependencies
        for (ct <- root +: sub; f <- ct.fields) {
          findDependencies(f.getType)
        }
      }

    case tt @ TupleType(bases) =>
      if (!(discovered contains t) && !(defined contains t)) {
        val sym = freshId("tuple"+bases.size)

        val c = Constructor(freshId(sym.name), tt, bases.zipWithIndex.map {
          case (tpe, i) => (freshId("_"+(i+1)), tpe)
        })

        discovered += (tt -> DataType(sym, Seq(c)))

        for (b <- bases) {
          findDependencies(b)
        }
      }

    case UnitType =>
      if (!(discovered contains t) && !(defined contains t)) {
        discovered += (t -> DataType(freshId("Unit"), Seq(Constructor(freshId("Unit"), t, Nil))))
      }

    case at @ ArrayType(base) =>
      if (!(discovered contains t) && !(defined contains t)) {
        val sym = freshId("array")

        val c = Constructor(freshId(sym.name), at, List(
          (freshId("size"), Int32Type),
          (freshId("content"), RawArrayType(Int32Type, base))
        ))

        discovered += (at -> DataType(sym, Seq(c)))

        findDependencies(base)
      }

    case tp @ TypeParameter(id) =>
      if (!(discovered contains t) && !(defined contains t)) {
        val sym = freshId(id.name)

        val c = Constructor(freshId(sym.name), tp, List(
          (freshId("val"), IntegerType)
        ))

        discovered += (tp -> DataType(sym, Seq(c)))
      }

    case _ =>
  }
}
