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


  /** Generic type bounds between two types. Serves as a base for a set of subtyping/unification functions.
    * It will allow subtyping between classes (but type parameters are invariant).
    * It will also allow a set of free parameters to be unified if needed.
    *
    * @param allowSub Allow subtyping for class types
    * @param freeParams The unifiable type parameters
    * @param isLub Whether the bound calculated is the LUB
    * @return An optional pair of (type, map) where type the resulting type bound
    *         (with type parameters instantiated as needed)
    *         and map the assignment of type variables.
    *         Result is empty if types are incompatible.
    * @see [[leastUpperBound]], [[greatestLowerBound]], [[isSubtypeOf]], [[typesCompatible]], [[unify]]
    */
  def typeBound(t1: TypeTree, t2: TypeTree, isLub: Boolean, allowSub: Boolean)
               (implicit freeParams: Seq[TypeParameter]): Option[(TypeTree, Map[TypeParameter, TypeTree])] = {

    def flatten(res: Seq[Option[(TypeTree, Map[TypeParameter, TypeTree])]]): Option[(Seq[TypeTree], Map[TypeParameter, TypeTree])] = {
      val (tps, subst) = res.map(_.getOrElse(return None)).unzip
      val flat = subst.flatMap(_.toSeq).groupBy(_._1)
      Some((tps, flat.mapValues { vs =>
        vs.map(_._2).distinct match {
          case Seq(unique) => unique
          case _ => return None
        }
      }))
    }

    (t1, t2) match {
      case (_: TypeParameter, _: TypeParameter) if t1 == t2 =>
        Some((t1, Map()))

      case (t, tp1: TypeParameter) if (freeParams contains tp1) && !(typeParamsOf(t) contains tp1) =>
        Some((t, Map(tp1 -> t)))

      case (tp1: TypeParameter, t) if (freeParams contains tp1) && !(typeParamsOf(t) contains tp1) =>
        Some((t, Map(tp1 -> t)))

      case (_: TypeParameter, _) =>
        None

      case (_, _: TypeParameter) =>
        None

      case (ct1: ClassType, ct2: ClassType) =>
        val cd1 = ct1.classDef
        val cd2 = ct2.classDef
        val bound: Option[ClassDef] = if (allowSub) {
          val an1 = cd1 +: cd1.ancestors
          val an2 = cd2 +: cd2.ancestors
          if (isLub) {
            (an1.reverse zip an2.reverse)
              .takeWhile(((_: ClassDef) == (_: ClassDef)).tupled)
              .lastOption.map(_._1)
          } else {
            // Lower bound
            if(an1.contains(cd2)) Some(cd1)
            else if (an2.contains(cd1)) Some(cd2)
            else None
          }
        } else {
          (cd1 == cd2).option(cd1)
        }
        for {
          cd <- bound
          (subs, map) <- flatten((ct1.tps zip ct2.tps).map { case (tp1, tp2) =>
            // Class types are invariant!
            typeBound(tp1, tp2, isLub, allowSub = false)
          })
        } yield (cd.typed(subs), map)

      case (FunctionType(from1, to1), FunctionType(from2, to2)) =>
        if (from1.size != from2.size) None
        else {
          val in = (from1 zip from2).map { case (tp1, tp2) =>
            typeBound(tp1, tp2, !isLub, allowSub) // Contravariant args
          }
          val out = typeBound(to1, to2, isLub, allowSub) // Covariant result
          flatten(out +: in) map {
            case (Seq(newTo, newFrom@_*), map) =>
              (FunctionType(newFrom, newTo), map)
          }
        }

      case Same(t1, t2) =>
        // Only tuples are covariant
        def allowVariance = t1 match {
          case _ : TupleType => true
          case _ => false
        }
        val NAryType(ts1, recon) = t1
        val NAryType(ts2, _) = t2
        if (ts1.size == ts2.size) {
          flatten((ts1 zip ts2).map { case (tp1, tp2) =>
            typeBound(tp1, tp2, isLub, allowSub = allowVariance)
          }).map { case (subs, map) => (recon(subs), map) }
        } else None

      case _ =>
        None
    }
  }

  def unify(tp1: TypeTree, tp2: TypeTree, freeParams: Seq[TypeParameter]) =
    typeBound(tp1, tp2, isLub = true, allowSub = false)(freeParams).map(_._2)

  /** Will try to instantiate superT so that subT <: superT
    *
    * @return Mapping of instantiations
    */
  def subtypingInstantiation(subT: TypeTree, superT: TypeTree) =
    typeBound(subT, superT, isLub = true, allowSub = true)(typeParamsOf(superT).toSeq) collect {
      case (tp, map) if instantiateType(superT, map) == tp => map
    }

  def leastUpperBound(tp1: TypeTree, tp2: TypeTree): Option[TypeTree] =
    typeBound(tp1, tp2, isLub = true, allowSub = true)(Seq()).map(_._1)

  def greatestLowerBound(tp1: TypeTree, tp2: TypeTree): Option[TypeTree] =
    typeBound(tp1, tp2, isLub = false, allowSub = true)(Seq()).map(_._1)

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

  def bestRealType(t: TypeTree) : TypeTree = t match {
    case (c: ClassType) => c.root
    case NAryType(tps, builder) => builder(tps.map(bestRealType))
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
