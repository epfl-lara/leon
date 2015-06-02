package leon
package solvers

import purescala.Types._
import purescala.Common._

case class DataType(sym: Identifier, cases: Seq[Constructor])
case class Constructor(sym: Identifier, tpe: TypeTree, fields: Seq[(Identifier, TypeTree)])

class ADTManager {
  protected def freshId(id: Identifier): Identifier = freshId(id.name)
  protected def freshId(name: String): Identifier = FreshIdentifier(name)

  protected def getHierarchy(ct: ClassType): (ClassType, Seq[CaseClassType]) = ct match {
    case act: AbstractClassType =>
      (act, act.knownCCDescendents)
    case cct: CaseClassType =>
      cct.parent match {
        case Some(p) =>
          getHierarchy(p)
        case None =>
          (cct, List(cct))
      }
  }

  protected var defined = Set[TypeTree]()

  def defineADT(t: TypeTree): Map[TypeTree, DataType] = {
    val adts = findDependencies(t)
    for ((t, dt) <- adts) {
      defined += t
    }
    adts
  }

  protected def findDependencies(t: TypeTree, dts: Map[TypeTree, DataType] = Map()): Map[TypeTree, DataType] = t match {
    case ct: ClassType =>
      val (root, sub) = getHierarchy(ct)

      if (!(dts contains root) && !(defined contains root)) {
        val sym = freshId(ct.id)

        val conss = sub.map { case cct =>
          Constructor(freshId(cct.id), cct, cct.fields.map(vd => (freshId(vd.id), vd.getType)))
        }

        var cdts = dts + (root -> DataType(sym, conss))

        // look for dependencies
        for (ct <- root +: sub; f <- ct.fields) {
          cdts ++= findDependencies(f.getType, cdts)
        }

        cdts
      } else {
        dts
      }

    case tt @ TupleType(bases) =>
      if (!(dts contains t) && !(defined contains t)) {
        val sym = freshId("tuple"+bases.size)

        val c = Constructor(freshId(sym.name), tt, bases.zipWithIndex.map {
          case (tpe, i) => (freshId("_"+(i+1)), tpe)
        })

        var cdts = dts + (tt -> DataType(sym, Seq(c)))

        for (b <- bases) {
          cdts ++= findDependencies(b, cdts)
        }
        cdts
      } else {
        dts
      }

    case UnitType =>
      if (!(dts contains t) && !(defined contains t)) {

        val sym = freshId("Unit")

        dts + (t -> DataType(sym, Seq(Constructor(freshId(sym.name), t, Nil))))
      } else {
        dts
      }

    case at @ ArrayType(base) =>
      if (!(dts contains t) && !(defined contains t)) {
        val sym = freshId("array")

        val c = Constructor(freshId(sym.name), at, List(
          (freshId("size"), Int32Type),
          (freshId("content"), RawArrayType(Int32Type, base))
        ))

        val cdts = dts + (at -> DataType(sym, Seq(c)))

        findDependencies(base, cdts)
      } else {
        dts
      }

    case _ =>
      dts
  }
}
