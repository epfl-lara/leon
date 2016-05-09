/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import Types._
import Definitions._
import Common._
import Expressions._

object TypeOps extends GenTreeOps[TypeTree] {

  val Deconstructor = NAryType

  def typeParamsOf(expr: Expr): Set[TypeParameter] = {
    ExprOps.collect(e => typeParamsOf(e.getType))(expr)
  }

  def typeParamsOf(t: TypeTree): Set[TypeParameter] = t match {
    case tp: TypeParameter => Set(tp)
    case NAryType(subs, _) =>
      subs.flatMap(typeParamsOf).toSet
  }

  def canBeSubtypeOf(
    tpe: TypeTree,
    freeParams: Seq[TypeParameter],
    stpe: TypeTree,
    lhsFixed: Boolean = false,
    rhsFixed: Boolean = false
  ): Option[Map[TypeParameter, TypeTree]] = {

    def unify(res: Seq[Option[Map[TypeParameter, TypeTree]]]): Option[Map[TypeParameter, TypeTree]] = {
      if (res.forall(_.isDefined)) {
        var result = Map[TypeParameter, TypeTree]()

        for (Some(m) <- res; (f, t) <- m) {
          result.get(f) match {
            case Some(t2) if t != t2 => return None
            case _ => result += (f -> t)
          }
        }

        Some(result)
      } else {
        None
      }
    }

    if (freeParams.isEmpty) {
      if (isSubtypeOf(tpe, stpe)) {
        Some(Map())
      } else {
        None
      }
    } else {
      (tpe, stpe) match {
        case (t1, t2) if t1 == t2 =>
          Some(Map())

        case (t, tp1: TypeParameter) if (freeParams contains tp1) && (!rhsFixed) && !(typeParamsOf(t) contains tp1) =>
          Some(Map(tp1 -> t))

        case (tp1: TypeParameter, t) if (freeParams contains tp1) && (!lhsFixed) && !(typeParamsOf(t) contains tp1) =>
          Some(Map(tp1 -> t))

        case (ct1: ClassType, ct2: ClassType) =>
          val rt1 = ct1.root
          val rt2 = ct2.root


          if (rt1.classDef == rt2.classDef) {
            unify((rt1.tps zip rt2.tps).map { case (tp1, tp2) =>
              canBeSubtypeOf(tp1, freeParams, tp2, lhsFixed, rhsFixed)
            })
          } else {
            None
          }

        case (_: TupleType, _: TupleType) |
             (_: SetType, _: SetType) |
             (_: MapType, _: MapType) |
             (_: BagType, _: BagType) |
             (_: FunctionType, _: FunctionType) =>

          val NAryType(ts1, _) = tpe
          val NAryType(ts2, _) = stpe

          if (ts1.size == ts2.size) {
            unify((ts1 zip ts2).map { case (tp1, tp2) =>
              canBeSubtypeOf(tp1, freeParams, tp2, lhsFixed, rhsFixed)
            })
          } else {
            None
          }

        case (t1, t2) =>
          None
      }
    }
  }

  def bestRealType(t: TypeTree) : TypeTree = t match {
    case (c: ClassType) => c.root
    case NAryType(tps, builder) => builder(tps.map(bestRealType))
  }

  def leastUpperBound(t1: TypeTree, t2: TypeTree): Option[TypeTree] = (t1,t2) match {
    case (c1: ClassType, c2: ClassType) =>

      def computeChain(ct: ClassType): List[ClassType] = ct.parent match {
        case Some(pct) =>
          computeChain(pct) ::: List(ct)
        case None =>
          List(ct)
      }

      val chain1 = computeChain(c1)
      val chain2 = computeChain(c2)

      val prefix = (chain1 zip chain2).takeWhile { case (ct1, ct2) => ct1 == ct2 }.map(_._1)

      prefix.lastOption

    case (TupleType(args1), TupleType(args2)) =>
      val args = (args1 zip args2).map(p => leastUpperBound(p._1, p._2))
      if (args.forall(_.isDefined)) Some(TupleType(args.map(_.get))) else None

    case (FunctionType(from1, to1), FunctionType(from2, to2)) =>
      val args = (from1 zip from2).map(p => greatestLowerBound(p._1, p._2))
      if (args.forall(_.isDefined)) {
        leastUpperBound(to1, to2) map { FunctionType(args.map(_.get), _) }
      } else {
        None
      }

    case (o1, o2) if o1 == o2 => Some(o1)
    case _ => None
  }

  def greatestLowerBound(t1: TypeTree, t2: TypeTree): Option[TypeTree] = (t1,t2) match {
    case (c1: ClassType, c2: ClassType) =>

      def computeChains(ct: ClassType): Set[ClassType] = ct.parent match {
        case Some(pct) =>
          computeChains(pct) + ct
        case None =>
          Set(ct)
      }

      if (computeChains(c1)(c2)) {
        Some(c2)
      } else if (computeChains(c2)(c1)) {
        Some(c1)
      } else {
        None
      }

    case (TupleType(args1), TupleType(args2)) =>
      val args = (args1 zip args2).map(p => greatestLowerBound(p._1, p._2))
      if (args.forall(_.isDefined)) Some(TupleType(args.map(_.get))) else None

    case (FunctionType(from1, to1), FunctionType(from2, to2)) =>
      val args = (from1 zip from2).map(p => leastUpperBound(p._1, p._2))
      if (args.forall(_.isDefined)) {
        greatestLowerBound(to1, to2).map { FunctionType(args.map(_.get), _) }
      } else {
        None
      }

    case (o1, o2) if o1 == o2 => Some(o1)
    case _ => None
  }

  def leastUpperBound(ts: Seq[TypeTree]): Option[TypeTree] = {
    def olub(ot1: Option[TypeTree], t2: Option[TypeTree]): Option[TypeTree] = ot1 match {
      case Some(t1) => leastUpperBound(t1, t2.get)
      case None => None
    }

    if (ts.isEmpty) {
      None
    } else {
      ts.map(Some(_)).reduceLeft(olub)
    }
  }

  def isSubtypeOf(t1: TypeTree, t2: TypeTree): Boolean = {
    leastUpperBound(t1, t2) == Some(t2)
  }

  def typesCompatible(t1: TypeTree, t2: TypeTree) = {
    leastUpperBound(t1, t2).isDefined
  }

  def typeCheck(obj: Expr, exps: TypeTree*) {
    val res = exps.exists(e => isSubtypeOf(obj.getType, e))

    if (!res) {
      throw TypeErrorException(obj, exps.toList)
    }
  }

  def isParametricType(tpe: TypeTree): Boolean = tpe match {
    case (tp: TypeParameter) => true
    case NAryType(tps, builder) => tps.exists(isParametricType)
  }

  // Helpers for instantiateType
  private def typeParamSubst(map: Map[TypeParameter, TypeTree])(tpe: TypeTree): TypeTree = tpe match {
    case (tp: TypeParameter) => map.getOrElse(tp, tp)
    case NAryType(tps, builder) => builder(tps.map(typeParamSubst(map)))
  }

  private def freshId(id: Identifier, newTpe: TypeTree) = {
    if (id.getType != newTpe) {
      FreshIdentifier(id.name, newTpe).copiedFrom(id)
    } else {
      id
    }
  }

  def instantiateType(id: Identifier, tps: Map[TypeParameterDef, TypeTree]): Identifier = {
    freshId(id, typeParamSubst(tps map { case (tpd, tp) => tpd.tp -> tp })(id.getType))
  }

  def instantiateType(tpe: TypeTree, tps: Map[TypeParameterDef, TypeTree]): TypeTree = {
    if (tps.isEmpty) {
      tpe
    } else {
      typeParamSubst(tps.map { case (tpd, tp) => tpd.tp -> tp })(tpe)
    }
  }

  def instantiateType(e: Expr, tps: Map[TypeParameterDef, TypeTree], ids: Map[Identifier, Identifier]): Expr = {
    if (tps.isEmpty && ids.isEmpty) {
      e
    } else {
      val tpeSub = if (tps.isEmpty) {
        { (tpe: TypeTree) => tpe }
      } else {
        typeParamSubst(tps.map { case (tpd, tp) => tpd.tp -> tp }) _
      }

      val transformer = new TreeTransformer {
        override def transform(id: Identifier): Identifier = freshId(id, transform(id.getType))
        override def transform(tpe: TypeTree): TypeTree = tpeSub(tpe)
      }

      transformer.transform(e)(ids)
    }
  }

  def typeCardinality(tp: TypeTree): Option[Int] = tp match {
    case Untyped => Some(0)
    case BooleanType => Some(2)
    case UnitType => Some(1)
    case SetType(base) =>
      typeCardinality(base).map(b => Math.pow(2, b).toInt)
    case FunctionType(from, to) =>
      val t = typeCardinality(to).getOrElse(return None)
      val f = from.map(typeCardinality).map(_.getOrElse(return None)).product
      Some(Math.pow(t, f).toInt)
    case MapType(from, to) =>
      for {
        t <- typeCardinality(to)
        f <- typeCardinality(from)
      } yield {
        Math.pow(t + 1, f).toInt
      }
    case cct: CaseClassType =>
      Some(cct.fieldsTypes.map { tpe =>
        typeCardinality(tpe).getOrElse(return None)
      }.product)
    case act: AbstractClassType =>
      val possibleChildTypes = leon.utils.fixpoint((tpes: Set[TypeTree]) => {
        tpes.flatMap(tpe => 
          Set(tpe) ++ (tpe match {
            case cct: CaseClassType => cct.fieldsTypes
            case act: AbstractClassType => Set(act) ++ act.knownCCDescendants
            case _ => Set.empty
          })
        )
      })(act.knownCCDescendants.toSet)
      if(possibleChildTypes(act)) return None
      Some(act.knownCCDescendants.map(typeCardinality).map(_.getOrElse(return None)).sum)
    case _ => None
  }

}
