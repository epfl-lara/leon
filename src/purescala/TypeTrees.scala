package funcheck.purescala

object TypeTrees {
  import Common._
  import Trees._
  import Definitions._

  trait Typed {
    self =>

    var _type: Option[TypeTree] = None

    def getType: TypeTree = _type match {
      case None => NoType
      case Some(t) => t
    }

    def setType(tt: TypeTree): self.type = _type match {
      case None => _type = Some(tt); this
      case Some(_) => scala.Predef.error("Resetting type information.")
    }
  }

  sealed abstract class TypeTree {
    override def toString: String = PrettyPrinter(this)
  }

  case object NoType extends TypeTree

  case object AnyType extends TypeTree
  case object BooleanType extends TypeTree
  case object Int32Type extends TypeTree

  case class ListType(base: TypeTree) extends TypeTree
  case class TupleType(bases: Seq[TypeTree]) extends TypeTree { lazy val dimension: Int = bases.length }
  case class FunctionType(arg: TypeTree, res: TypeTree) extends TypeTree
  case class SetType(base: TypeTree) extends TypeTree
  // case class MultisetType(base: TypeTree) extends TypeTree
  case class MapType(from: TypeTree, to: TypeTree) extends TypeTree
  case class ClassType(id: Identifier) extends TypeTree
  case class CaseClassType(id: Identifier) extends TypeTree
  case class OptionType(base: TypeTree) extends TypeTree
}
