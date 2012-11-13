package leon
package purescala

object TypeTrees {
  import Common._
  import Trees._
  import Definitions._

  trait Typed extends Serializable {
    self =>

    private var _type: Option[TypeTree] = None

    def getType: TypeTree = _type match {
      case None => Untyped
      case Some(t) => t
    }

    def setType(tt: TypeTree): self.type = _type match {
      case None => _type = Some(tt); this
      case Some(o) if o != tt => scala.sys.error("Resetting type information! Type [" + o + "] is modified to [" + tt)
      case _ => this
    }
  }

  trait FixedType extends Typed {
    self =>

    val fixedType: TypeTree
    override def getType: TypeTree = fixedType
    override def setType(tt2: TypeTree) : self.type = this
  }
    

  sealed abstract class TypeTree extends Serializable {
    override def toString: String = PrettyPrinter(this)
  }

  // Sort of a quick hack...
  def bestRealType(t: TypeTree) : TypeTree = t match {
    case c: ClassType if c.classDef.isInstanceOf[CaseClassDef] => {
      c.classDef.parent match {
        case None => scala.sys.error("Asking for real type of a case class without abstract parent")
        case Some(p) => AbstractClassType(p)
      }
    }
    case other => other
  }

  def leastUpperBound(t1: TypeTree, t2: TypeTree): Option[TypeTree] = (t1,t2) match {
    case (c1: ClassType, c2: ClassType) => {
      import scala.collection.immutable.Set
      var c: ClassTypeDef = c1.classDef
      var visited: Set[ClassTypeDef] = Set(c)

      while(c.parent.isDefined) {
        c = c.parent.get
        visited = visited ++ Set(c)
      }

      c = c2.classDef
      var found: Option[ClassTypeDef] = if(visited.contains(c)) {
        Some(c)
      } else {
        None
      }

      while(found.isEmpty && c.parent.isDefined) {
        c = c.parent.get
        if(visited.contains(c))
          found = Some(c)
      }

      if(found.isEmpty) {
        None
      } else {
        Some(classDefToClassType(found.get))
      }
    }

    case (o1, o2) if (o1 == o2) => Some(o1)
    case (o1,BottomType) => Some(o1)
    case (BottomType,o2) => Some(o2)
    case (o1,AnyType) => Some(AnyType)
    case (AnyType,o2) => Some(AnyType)

    case _ => None
  }

  def isSubtypeOf(t1: TypeTree, t2: TypeTree): Boolean = {
    leastUpperBound(t1, t2) == Some(t2)
  }

  // returns the number of distinct values that inhabit a type
  sealed abstract class TypeSize extends Serializable
  case class FiniteSize(size: Int) extends TypeSize
  case object InfiniteSize extends TypeSize

  def domainSize(typeTree: TypeTree) : TypeSize = typeTree match {
    case Untyped => FiniteSize(0)
    case AnyType => InfiniteSize
    case BottomType => FiniteSize(0)
    case BooleanType => FiniteSize(2)
    case UnitType => FiniteSize(1)
    case Int32Type => InfiniteSize
    case ListType(_) => InfiniteSize
    case ArrayType(_) => InfiniteSize
    case TupleType(bases) => {
      val baseSizes = bases.map(domainSize(_))
      baseSizes.find(_ == InfiniteSize) match {
        case Some(_) => InfiniteSize
        case None => FiniteSize(baseSizes.map(_.asInstanceOf[FiniteSize].size).reduceLeft(_ * _))
      }
    }
    case SetType(base) => domainSize(base) match {
      case InfiniteSize => InfiniteSize
      case FiniteSize(n) => FiniteSize(scala.math.pow(2, n).toInt)
    }
    case MultisetType(_) => InfiniteSize
    case MapType(from,to) => (domainSize(from),domainSize(to)) match {
      case (InfiniteSize,_) => InfiniteSize
      case (_,InfiniteSize) => InfiniteSize
      case (FiniteSize(n),FiniteSize(m)) => FiniteSize(scala.math.pow(m+1, n).toInt)
    }
    case OptionType(base) => domainSize(base) match {
      case InfiniteSize => InfiniteSize
      case FiniteSize(n) => FiniteSize(n+1)
    }
    case FunctionType(fts, tt) => {
      val fromSizes = fts map domainSize
      val toSize = domainSize(tt)
      if (fromSizes.exists(_ == InfiniteSize) || toSize == InfiniteSize)
        InfiniteSize
      else {
        val n = toSize.asInstanceOf[FiniteSize].size
        FiniteSize(scala.math.pow(n, fromSizes.foldLeft(1)((acc, s) => acc * s.asInstanceOf[FiniteSize].size)).toInt)
      }
    }
    case c: ClassType => InfiniteSize
  }

  case object Untyped extends TypeTree
  case object AnyType extends TypeTree
  case object BottomType extends TypeTree // This type is useful when we need an underlying type for None, Set.empty, etc. It should always be removed after parsing, though.
  case object BooleanType extends TypeTree
  case object Int32Type extends TypeTree
  case object UnitType extends TypeTree

  case class ListType(base: TypeTree) extends TypeTree
  case class TupleType(bases: Seq[TypeTree]) extends TypeTree { lazy val dimension: Int = bases.length }
  case class SetType(base: TypeTree) extends TypeTree
  case class MultisetType(base: TypeTree) extends TypeTree
  case class MapType(from: TypeTree, to: TypeTree) extends TypeTree
  case class OptionType(base: TypeTree) extends TypeTree
  case class FunctionType(from: List[TypeTree], to: TypeTree) extends TypeTree
  case class ArrayType(base: TypeTree) extends TypeTree

  sealed abstract class ClassType extends TypeTree {
    val classDef: ClassTypeDef
    val id: Identifier = classDef.id

    override def hashCode : Int = id.hashCode
    override def equals(that : Any) : Boolean = that match {
      case t : ClassType => t.id == this.id
      case _ => false
    }
  }
  case class AbstractClassType(classDef: AbstractClassDef) extends ClassType
  case class CaseClassType(classDef: CaseClassDef) extends ClassType

  def classDefToClassType(cd: ClassTypeDef): ClassType = cd match {
    case a: AbstractClassDef => AbstractClassType(a)
    case c: CaseClassDef => CaseClassType(c)
  }
}
