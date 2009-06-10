package funcheck.purescala

object TypeTrees {
  import Common._
  import Trees._
  import Definitions._

  trait Typed {
    def getType: TypeTree
  }

  sealed abstract class TypeTree {
    override def toString: String = PrettyPrinter(this)
  }

  case object AnyType extends TypeTree
  case object BooleanType extends TypeTree
  case object Int32Type extends TypeTree

  case class ListType(base: TypeTree) extends TypeTree
  case class TupleType(bases: Seq[TypeTree]) extends TypeTree { lazy val dimension: Int = bases.length }
  case class FunctionType(arg: TypeTree, res: TypeTree) extends TypeTree
  case class SetType(base: TypeTree) extends TypeTree
  case class MultisetType(base: TypeTree) extends TypeTree
  case class MapType(from: TypeTree, to: TypeTree) extends TypeTree
  case class ClassType(id: Identifier) extends TypeTree
  case class CaseClassType(id: Identifier) extends TypeTree
  case class OptionType(base: TypeTree) extends TypeTree
}
