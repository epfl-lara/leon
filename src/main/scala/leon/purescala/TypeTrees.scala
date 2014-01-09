/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package purescala

object TypeTrees {
  import Common._
  import Trees._
  import TypeTreeOps._
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
      case Some(o) if leastUpperBound(o, tt) == Some(tt) => _type = Some(tt); this
      case Some(o) => scala.sys.error("Resetting type information of " + this + " [" + this.getClass + "] ! " +
          o + " [" + o.getClass + "] is modified to " + tt + " [" + tt.getClass + "]")
    }

    def isTyped : Boolean = (getType != Untyped)
  }

  class TypeErrorException(msg: String) extends Exception(msg)

  object TypeErrorException {
    def apply(obj: Expr, exp: List[TypeTree]): TypeErrorException = {
      new TypeErrorException("Type error: "+obj+", expected: "+exp.mkString(" or ")+", found "+obj.getType)
    }

    def apply(obj: Expr, exp: TypeTree): TypeErrorException = {
      apply(obj, List(exp))
    }
  }

  def typeCheck(obj: Expr, exps: TypeTree*) {
    val res = exps.exists(e => isSubtypeOf(obj.getType, e))

    if (!res) {
      throw TypeErrorException(obj, exps.toList)
    }
  }

  trait FixedType extends Typed {
    self =>

    val fixedType: TypeTree
    override def getType: TypeTree = fixedType
    override def setType(tt2: TypeTree) : self.type = this
  }
    

  sealed abstract class TypeTree extends Tree {
    override def toString: String = PrettyPrinter(this)
  }

  // Sort of a quick hack...
  def bestRealType(t: TypeTree) : TypeTree = t match {
    case c: CaseClassType => c.parent match {
      case None => c
      case Some(p) => p
    }
    case other => other
  }

  def leastUpperBound(t1: TypeTree, t2: TypeTree): Option[TypeTree] = (t1,t2) match {
    case (c1: ClassType, c2: ClassType) => {
      import scala.collection.immutable.Set
      var c: ClassType = c1
      var visited: Set[ClassType] = Set(c)

      while(c.parent.isDefined) {
        c = c.parent.get
        visited = visited ++ Set(c)
      }

      c = c2
      var found: Option[ClassType] = if(visited.contains(c)) {
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
        Some(found.get)
      }
    }
    case (TupleType(args1), TupleType(args2)) if args1.size == args2.size =>
      val args = (args1 zip args2).map(p => leastUpperBound(p._1, p._2))
      if (args.forall(_.isDefined)) Some(TupleType(args.map(_.get))) else None
    case (o1, o2) if (o1 == o2) => Some(o1)
    case (o1, Untyped) => Some(o1)
    case (Untyped, o2) => Some(o2)
    case (o1,BottomType) => Some(o1)
    case (BottomType,o2) => Some(o2)
    case (o1,AnyType) => Some(AnyType)
    case (AnyType,o2) => Some(AnyType)
    case (FunctionType(args1, ret1), FunctionType(args2, ret2)) =>
      val args = (args1 zip args2).map(p => highestLowerBound(p._1, p._2))
      val ret = leastUpperBound(ret1, ret2)
      if (args.exists(!_.isDefined) || !ret.isDefined) None else Some(FunctionType(args.map(_.get), ret.get))
    case (MapType(from1, to1), MapType(from2, to2)) if from1 == from2 => leastUpperBound(to1, to2).map(tpe => MapType(from1, tpe))
    case (ArrayType(base1), ArrayType(base2)) => leastUpperBound(base1, base2).map(tpe => ArrayType(tpe))
    case (ListType(base1), ListType(base2)) => leastUpperBound(base1, base2).map(tpe => ListType(tpe))
    case (SetType(base1), SetType(base2)) => leastUpperBound(base1, base2).map(tpe => SetType(tpe))
    case (MultisetType(base1), MultisetType(base2)) => leastUpperBound(base1, base2).map(tpe => MultisetType(tpe))
    case _ => None
  }
  
  def leastUpperBound(ts: Seq[TypeTree]): Option[TypeTree] = {
    def olub(ot1: Option[TypeTree], t2: Option[TypeTree]): Option[TypeTree] = ot1 match {
      case Some(t1) => leastUpperBound(t1, t2.get)
      case None => None
    }

    ts.map(Some(_)).reduceLeft(olub)
  }

  def highestLowerBound(t1: TypeTree, t2: TypeTree): Option[TypeTree] = (t1,t2) match {
    // this is easy since we don't have any traits or stuff, we just check that one
    // class is parent of the other and we're done! 
    case (c1: ClassType, c2: ClassType) => {
      import scala.collection.immutable.Set
      def parentsOf(c: ClassType): Set[ClassType] = c.parent match {
        case Some(parent) => parentsOf(parent) + parent
        case None => Set.empty
      }

      if (c1 == c2) Some(c1)
      else if (parentsOf(c1)(c2)) Some(c1)
      else if (parentsOf(c2)(c1)) Some(c2)
      else None
    }
    case (o1, o2) if (o1 == o2) => Some(o1)
    case (o1,BottomType) => Some(BottomType)
    case (BottomType,o2) => Some(BottomType)
    case (o1,AnyType) => Some(o1)
    case (AnyType,o2) => Some(o2)
    case (FunctionType(args1, ret1), FunctionType(args2, ret2)) =>
      val args = (args1 zip args2).map(p => highestLowerBound(p._1, p._2))
      val ret = leastUpperBound(ret1, ret2)
      if (args.exists(!_.isDefined) || !ret.isDefined) None else Some(FunctionType(args.map(_.get), ret.get))
    case (TupleType(tpes1), TupleType(tpes2)) if tpes1.size == tpes2.size =>
      val bounds = (tpes1 zip tpes2).map(p => highestLowerBound(p._1, p._2))
      if (bounds.exists(!_.isDefined)) None else Some(TupleType(bounds.map(_.get)))
    case (MapType(from1, to1), MapType(from2, to2)) if from1 == from2 => highestLowerBound(to1, to2).map(tpe => MapType(from1, tpe))
    case (ArrayType(base1), ArrayType(base2)) => highestLowerBound(base1, base2).map(tpe => ArrayType(tpe))
    case (ListType(base1), ListType(base2)) => highestLowerBound(base1, base2).map(tpe => ListType(tpe))
    case (SetType(base1), SetType(base2)) => highestLowerBound(base1, base2).map(tpe => SetType(tpe))
    case (MultisetType(base1), MultisetType(base2)) => highestLowerBound(base1, base2).map(tpe => MultisetType(tpe))
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

  case class TypeParameter(id: Identifier) extends TypeTree

  class TupleType private (val bases: Seq[TypeTree]) extends TypeTree {
    lazy val dimension: Int = bases.length

    override def equals(other: Any): Boolean = {
      other match {
        case (t: TupleType) => t.bases == bases
        case _ => false
      }
    }

    override def hashCode: Int = {
      bases.foldLeft(42)((acc, t) => acc + t.hashCode)
    }

  }
  object TupleType {
    def apply(bases: Seq[TypeTree]): TupleType = {
      new TupleType(bases.map(bestRealType(_)))
    }
    //TODO: figure out which of the two unapply is better
    //def unapply(t: TypeTree): Option[Seq[TypeTree]] = t match {
    //  case (tt: TupleType) => Some(tt.bases)
    //  case _ => None
    //}
    def unapply(tt: TupleType): Option[Seq[TypeTree]] = if(tt == null) None else Some(tt.bases)
  }
  object TupleOneType {
    def unapply(tt : TupleType) : Option[TypeTree] = if(tt == null) None else {
      if(tt.bases.size == 1) {
        Some(tt.bases.head)
      } else {
        None
      }
    }
  }

  case class ListType(base: TypeTree) extends TypeTree
  case class SetType(base: TypeTree) extends TypeTree
  case class MultisetType(base: TypeTree) extends TypeTree
  case class MapType(from: TypeTree, to: TypeTree) extends TypeTree
  case class FunctionType(from: Seq[TypeTree], to: TypeTree) extends TypeTree
  case class ArrayType(base: TypeTree) extends TypeTree

  sealed abstract class ClassType extends TypeTree {
    val classDef : ClassTypeDef
    val id       : Identifier = classDef.id
    val tparams  : Seq[TypeTree]

    protected lazy val typeMapping : Map[TypeTree, TypeTree] = (classDef.tparams.map(_.toType) zip tparams).toMap
    protected lazy val tdefMapping : Map[TypeParameterDef, TypeTree] = (classDef.tparams zip tparams).toMap

    override def hashCode : Int = (id, tparams).hashCode
    override def equals(that : Any) : Boolean = that match {
      case t : ClassType => (t.id, t.tparams) == (this.id, this.tparams)
      case _ => false
    }

    def parent: Option[AbstractClassType] = classDef.parent.map { pct =>
      val tparams = pct.tparams.map(replaceTypesFromTPs(typeMapping.get _, _))
      AbstractClassType(pct.classDef, tparams)
    }

    assert(classDef.tparams.size == tparams.size)
  }

  case class AbstractClassType(classDef: AbstractClassDef, tparams: Seq[TypeTree]) extends ClassType {
    private def getTParams(cd: ClassTypeDef) = cd match {
      case ccd : CaseClassDef =>
        val pairs = (ccd.parent.get.tparams zip tparams).flatMap(p => collectParametricMapping(p._1, p._2))
        val mapping = mergeParametricMapping(pairs).get
        ccd.tparams.map(tp => mapping.getOrElse(tp.toType, tp.toType))
      case acd : AbstractClassDef =>
        acd.tparams.map(_.toType)
    }

    def knownChildren : Seq[ClassType] = classDef.knownChildren.map(cd => classDefToClassType(cd, getTParams(cd)))

    def knownDescendents : Seq[ClassType] = classDef.knownDescendents.map(cd => classDefToClassType(cd, getTParams(cd)))
  }

  case class CaseClassType(classDef: CaseClassDef, tparams: Seq[TypeTree]) extends ClassType {
    def fields: VarDecls = classDef.fields.map { vd =>
      val id = vd.id.reType(replaceTypesFromTPs(typeMapping.get, vd.id.getType))
      VarDecl(id, id.getType)
    }

    def fieldsIds: Seq[Identifier] = fields.map(_.id)
  }

  def classDefToClassType(cd: ClassTypeDef, tparams: Seq[TypeTree]): ClassType = cd match {
    case a: AbstractClassDef => AbstractClassType(a, tparams)
    case c: CaseClassDef => CaseClassType(c, tparams)
  }
}
