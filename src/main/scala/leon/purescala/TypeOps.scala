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

  private class Unsolvable extends Exception
  private def unsolvable = throw new Unsolvable

  /** Produces an instantiation for a type so that it respects a type bound (upper or lower). */
  private def instantiation_<:>(toInst: TypeTree, bound: TypeTree, isUpper: Boolean): Option[Map[TypeParameter, TypeTree]] = {
    case class Subtyping(tp: TypeParameter, bound: TypeTree, isUpper: Boolean)

    def collectConstraints(toInst: TypeTree, bound: TypeTree, isUpper: Boolean): Seq[Subtyping] = (toInst, bound) match {
      case (_, Untyped) => unsolvable
      case (Untyped, _) => unsolvable
      case (tp: TypeParameter, _) => Seq(Subtyping(tp, bound, isUpper))
      case (ct1: ClassType, ct2: ClassType) =>
        val cd1 = ct1.classDef
        val cd2 = ct2.classDef
        val (cl, ch) = if (isUpper) (cd1, cd2) else (cd2, cd1)
        if (!((cl == ch) || (cl.ancestors contains ch))) unsolvable
        else {
          for {
            (t1, t2) <- ct1.tps zip ct2.tps
            variance <- Seq(true, false)
            constr <- collectConstraints(t1, t2, variance)
          } yield constr
        }
      case (FunctionType(from1, to1), FunctionType(from2, to2)) if from1.size == from2.size =>
        val in = (from1 zip from2).flatMap { case (tp1, tp2) =>
          collectConstraints(tp1, tp2, !isUpper) // Contravariant args
        }
        val out = collectConstraints(to1, to2, isUpper) // Covariant result
        in ++ out

      case (TupleType(ts1), TupleType(ts2)) if ts1.size == ts2.size =>
        (ts1 zip ts2).flatMap { case (tp1, tp2) =>
          collectConstraints(tp1, tp2, isUpper) // Covariant tuples
        }

      case Same(NAryType(ts1, _), NAryType(ts2, _)) if ts1.size == ts2.size =>
        for {
          (t1, t2) <- ts1 zip ts2
          variance <- Seq(true, false)
          constr <- collectConstraints(t1, t2, variance)
        } yield constr

      case _ => unsolvable
    }

    def solveConstraints(constraints: Seq[Subtyping]): Map[TypeParameter, TypeTree] = {
      val flattened = constraints.groupBy(_.tp)
      flattened.mapValues { cons =>
        val (supers, subs) = cons.partition(_.isUpper)
        // Lub of the variable will be the glb of its upper bounds
        val lub = leastUpperBound(subs.map(_.bound))
        // Glb of the variable will be the lub of its lower bounds
        val glb = greatestLowerBound(supers.map(_.bound))

        if (subs.isEmpty) glb        // No lower bounds
        else if (supers.isEmpty) lub // No upper bounds
        else if (isSubtypeOf(glb, lub)) lub // Both lower and upper bounds. If they are compatible, randomly return lub
        else unsolvable                     // Note: It is enough to use isSubtypeOf because lub and glb contain no type variables (of toInst)
      }.view.force
    }

    try {
      Some(solveConstraints(collectConstraints(toInst, bound, isUpper)))
    } catch {
      case _: Unsolvable =>
        None
    }

  }

  /** Computes the tightest bound (upper or lower) of two types */
  private def typeBound(tp1: TypeTree, tp2: TypeTree, upper: Boolean): TypeTree = {

    def classBound(cd1: ClassDef, cd2: ClassDef, upper: Boolean) = {
      val an1 = cd1 +: cd1.ancestors
      val an2 = cd2 +: cd2.ancestors
      if (upper) {
        // Upper bound
        (an1.reverse zip an2.reverse)
          .takeWhile(((_: ClassDef) == (_: ClassDef)).tupled)
          .lastOption.map(_._1)
      } else {
        // Lower bound
        if (an1.contains(cd2)) Some(cd1)
        else if (an2.contains(cd1)) Some(cd2)
        else None
      }
    }

    (tp1, tp2) match {
      case (ct1: ClassType, ct2: ClassType) =>
        if (ct1.tps != ct2.tps) Untyped // invariant classtypes
        else {
          classBound(ct1.classDef, ct2.classDef, upper)
            .map(_.typed(ct1.tps))
            .getOrElse(Untyped).unveilUntyped
        }

      case (FunctionType(from1, to1), FunctionType(from2, to2)) =>
        if (from1.size != from2.size) Untyped
        else {
          val in = (from1 zip from2).map { case (tp1, tp2) =>
            typeBound(tp1, tp2, !upper) // Contravariant args
          }
          val out = typeBound(to1, to2, upper) // Covariant result
          FunctionType(in, out).unveilUntyped
        }

      case (bv1: BitVectorType, bv2: BitVectorType) =>
        List(bv1, bv2).maxBy(if (upper) _.size else - _.size)

      case (TupleType(ts1), TupleType(ts2)) =>
        if (ts1.size != ts2.size) Untyped
        else {
          val ts = (ts1 zip ts2).map { case (tp1, tp2) =>
            typeBound(tp1, tp2, upper) // Covariant tuples
          }
          TupleType(ts).unveilUntyped
        }

      case (t1, t2) =>
        // Everything else is invariant
        if (t1 == t2) t1.unveilUntyped else Untyped
    }
  }

  /** Computes the tightest bound (upper or lower) of a sequence of types */
  private def typeBound(tps: Seq[TypeTree], upper: Boolean): TypeTree = {
    if (tps.isEmpty) Untyped
    else tps.reduceLeft(typeBound(_, _, upper))
  }

  def leastUpperBound(tp1: TypeTree, tp2: TypeTree): TypeTree =
    typeBound(tp1, tp2, true)

  def leastUpperBound(tps: Seq[TypeTree]): TypeTree =
    typeBound(tps, true)

  def greatestLowerBound(tp1: TypeTree, tp2: TypeTree): TypeTree =
    typeBound(tp1, tp2, false)

  def greatestLowerBound(tps: Seq[TypeTree]): TypeTree =
    typeBound(tps, false)

  def isSubtypeOf(t1: TypeTree, t2: TypeTree): Boolean = {
    leastUpperBound(t1, t2) == t2
  }

  def typesCompatible(t1: TypeTree, t2: TypeTree) = {
    leastUpperBound(t1, t2) != Untyped
  }

  /** Instantiates a type so that it is subtype of another type */
  def instantiation_<:(subT: TypeTree, superT: TypeTree) =
    instantiation_<:>(subT, superT, isUpper = true)

  /** Instantiates a type so that it is supertype of another type */
  def instantiation_>:(superT: TypeTree, subT: TypeTree) =
    instantiation_<:>(superT, subT, isUpper = false)

  /** Unifies two types, under a set of free variables */
  def unify(t1: TypeTree, t2: TypeTree, free: Seq[TypeParameter]): Option[List[(TypeParameter, TypeTree)]] = {
    def collectConstraints(t1: TypeTree, t2: TypeTree): List[(TypeParameter, TypeTree)] = (t1, t2) match {
      case _ if t1 == t2 => Nil
      case (tp: TypeParameter, _) if !(typeParamsOf(t2) contains tp) && (free contains tp) =>
        List(tp -> t2)
      case (_, tp: TypeParameter) if !(typeParamsOf(t1) contains tp) && (free contains tp) =>
        List(tp -> t1)
      case (_: TypeParameter, _) =>
        unsolvable
      case (_, _: TypeParameter) =>
        unsolvable
      case (ct1: ClassType, ct2: ClassType) if ct1.classDef == ct2.classDef =>
        (ct1.tps zip ct2.tps).toList flatMap (collectConstraints _).tupled
      case Same(NAryType(ts1, _), NAryType(ts2, _)) if ts1.length == ts2.length =>
        (ts1 zip ts2).toList flatMap (collectConstraints _).tupled
      case _ => unsolvable
    }

    def solveConstraints(const: List[(TypeTree, TypeTree)]): List[(TypeParameter, TypeTree)] = {
      const match {
        case Nil => Nil
        case (tp: TypeParameter, t) :: tl =>
          val replaced = tl map { case (t1, t2) =>
            (instantiateType(t1, Map(tp -> t)), instantiateType(t2, Map(tp -> t)))
          }
          (tp -> t) :: solveConstraints(replaced)
        case (ct1: ClassType, ct2: ClassType) :: tl if ct1.classDef == ct2.classDef =>
          solveConstraints((ct1.tps zip ct2.tps).toList ++ tl)
        case Same(NAryType(ts1, _), NAryType(ts2, _)) :: tl if ts1.length == ts2.length =>
          solveConstraints( (ts1 zip ts2).toList ++ tl)
        case _ =>
          unsolvable
      }
    }

    try {
      Some(solveConstraints(collectConstraints(t1, t2)))
    } catch {
      case _: Unsolvable =>
        None
    }
  }

  def typeCheck(obj: Expr, exps: TypeTree*) {
    val res = exps.exists(e => isSubtypeOf(obj.getType, e))

    if (!res) {
      throw TypeErrorException(obj, exps.toList)
    }
  }

  def bestRealType(t: TypeTree) : TypeTree = t match {
    case (c: ClassType) => c.root
    case NAryType(tps, builder) => builder(tps.map(bestRealType))
  }

  def isParametricType(tpe: TypeTree): Boolean = tpe match {
    case (tp: TypeParameter) => true
    case NAryType(tps, builder) => tps.exists(isParametricType)
  }

  def isBVType(tpe: TypeTree): Boolean = tpe match {
    case bv: BitVectorType => true
    case _ => false
  }

  def areSameBVType(tpe1: TypeTree, tpe2: TypeTree): Boolean = (tpe1, tpe2) match {
    case (BVType(s1), BVType(s2)) if s1 == s2 => true
    case _ => false
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

  def instantiateType(id: Identifier, tps: Map[TypeParameter, TypeTree]): Identifier = {
    freshId(id, typeParamSubst(tps)(id.getType))
  }

  def instantiateType(tpe: TypeTree, tps: Map[TypeParameter, TypeTree]): TypeTree = {
    if (tps.isEmpty) {
      tpe
    } else {
      typeParamSubst(tps)(tpe)
    }
  }

  def instantiateType(e: Expr, tps: Map[TypeParameter, TypeTree], ids: Map[Identifier, Identifier]): Expr = {
    if (tps.isEmpty && ids.isEmpty) {
      e
    } else {
      val tpeSub = if (tps.isEmpty) {
        { (tpe: TypeTree) => tpe }
      } else {
        typeParamSubst(tps) _
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
    case TupleType(tps) =>
      Some(tps.map(typeCardinality).map(_.getOrElse(return None)).product)
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
