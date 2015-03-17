/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package purescala

import ExprOps.postMap
import Types._
import Definitions._
import Common._
import Expressions._
import Extractors._
import Constructors._

object TypeOps {
  def typeDepth(t: TypeTree): Int = t match {
    case NAryType(tps, builder) => 1+tps.foldLeft(0) { case (d, t) => d max typeDepth(t) }
  }

  def typeParamsOf(t: TypeTree): Set[TypeParameter] = t match {
    case tp: TypeParameter => Set(tp)
    case _ =>
      val NAryType(subs, _) = t
      subs.map(typeParamsOf).foldLeft(Set[TypeParameter]())(_ ++ _)
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
        case (t, tp1: TypeParameter) =>
          if ((freeParams contains tp1) && (!rhsFixed) && !(typeParamsOf(t) contains tp1)) {
            Some(Map(tp1 -> t))
          } else if (tp1 == t) {
            Some(Map())
          } else {
            None
          }

        case (tp1: TypeParameter, t) =>
          if ((freeParams contains tp1) && (!lhsFixed) && !(typeParamsOf(t) contains tp1)) {
            Some(Map(tp1 -> t))
          } else if (tp1 == t) {
            Some(Map())
          } else {
            None
          }

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
          if (t1 == t2) {
            Some(Map())
          } else {
            None
          }
      }
    }
  }

  def bestRealType(t: TypeTree) : TypeTree = t match {
    case (c: CaseClassType) => c.root
    case NAryType(tps, builder) => builder(tps.map(bestRealType))
  }

  def leastUpperBound(t1: TypeTree, t2: TypeTree): Option[TypeTree] = (t1,t2) match {
    case (c1: ClassType, c2: ClassType) =>
      import scala.collection.immutable.Set


      def computeChain(ct: ClassType): List[ClassType] = ct.parent match {
        case Some(pct) =>
          computeChain(pct) ::: List(ct)
        case None =>
          List(ct)
      }

      var chain1 = computeChain(c1)
      var chain2 = computeChain(c2)

      val prefix = (chain1 zip chain2).takeWhile { case (ct1, ct2) => ct1 == ct2 }.map(_._1)

      prefix.lastOption

    case (TupleType(args1), TupleType(args2)) =>
      val args = (args1 zip args2).map(p => leastUpperBound(p._1, p._2))
      if (args.forall(_.isDefined)) Some(TupleType(args.map(_.get))) else None
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


  def typeCheck(obj: Expr, exps: TypeTree*) {
    val res = exps.exists(e => isSubtypeOf(obj.getType, e))

    if (!res) {
      throw TypeErrorException(obj, exps.toList)
    }
  }

  def instantiateType(tpe: TypeTree, tps: Map[TypeParameterDef, TypeTree]): TypeTree = {
    if (tps.isEmpty) {
      tpe
    } else {
      typeParamSubst(tps.map { case (tpd, tp) => tpd.tp -> tp })(tpe)
    }
  }

  private def typeParamSubst(map: Map[TypeParameter, TypeTree])(tpe: TypeTree): TypeTree = tpe match {
    case (tp: TypeParameter) => map.getOrElse(tp, tp)
    case NAryType(tps, builder) => builder(tps.map(typeParamSubst(map)))
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

      def rec(idsMap: Map[Identifier, Identifier])(e: Expr): Expr = {
        def freshId(id: Identifier, newTpe: TypeTree) = {
          if (id.getType != newTpe) {
            FreshIdentifier(id.name, newTpe).copiedFrom(id)
          } else {
            id
          }
        }

        // Simple rec without affecting map
        val srec = rec(idsMap) _

        def onMatchLike(e: Expr, cases : Seq[MatchCase]) = {
        
          val newTpe = tpeSub(e.getType)
         
          def mapsUnion(maps: Seq[Map[Identifier, Identifier]]): Map[Identifier, Identifier] = {
            maps.foldLeft(Map[Identifier, Identifier]())(_ ++ _)
          }

          def trCase(c: MatchCase) = c match {
            case SimpleCase(p, b) => 
              val (newP, newIds) = trPattern(p, newTpe)
              SimpleCase(newP, rec(idsMap ++ newIds)(b))

            case GuardedCase(p, g, b) => 
              val (newP, newIds) = trPattern(p, newTpe)
              GuardedCase(newP, rec(idsMap ++ newIds)(g), rec(idsMap ++ newIds)(b))
          }

          def trPattern(p: Pattern, expType: TypeTree): (Pattern, Map[Identifier, Identifier]) = (p, expType) match {
            case (InstanceOfPattern(ob, ct), _) =>
              val newCt = tpeSub(ct).asInstanceOf[ClassType]
              val newOb = ob.map(id => freshId(id, newCt))

              (InstanceOfPattern(newOb, newCt), (ob zip newOb).toMap)

            case (TuplePattern(ob, sps), tpt @ TupleType(stps)) =>
              val newOb = ob.map(id => freshId(id, tpt))

              val (newSps, newMaps) = (sps zip stps).map { case (sp, stpe) => trPattern(sp, stpe) }.unzip

              (TuplePattern(newOb, newSps), (ob zip newOb).toMap ++ mapsUnion(newMaps))

            case (CaseClassPattern(ob, cct, sps), _) =>
              val newCt = tpeSub(cct).asInstanceOf[CaseClassType]

              val newOb = ob.map(id => freshId(id, newCt))

              val (newSps, newMaps) = (sps zip newCt.fieldsTypes).map { case (sp, stpe) => trPattern(sp, stpe) }.unzip

              (CaseClassPattern(newOb, newCt, newSps), (ob zip newOb).toMap ++ mapsUnion(newMaps))

            case (WildcardPattern(ob), expTpe) =>
              val newOb = ob.map(id => freshId(id, expTpe))

              (WildcardPattern(newOb), (ob zip newOb).toMap)

            case (LiteralPattern(ob, lit), expType) => 
              val newOb = ob.map(id => freshId(id, expType))
              (LiteralPattern(newOb,lit), (ob zip newOb).toMap)

            case _ =>
              sys.error("woot!?")
          }

          (srec(e), cases.map(trCase))//.copiedFrom(m)
        }

        e match {
          case fi @ FunctionInvocation(TypedFunDef(fd, tps), args) =>
            FunctionInvocation(TypedFunDef(fd, tps.map(tpeSub)), args.map(srec)).copiedFrom(fi)

          case cc @ CaseClass(ct, args) =>
            CaseClass(tpeSub(ct).asInstanceOf[CaseClassType], args.map(srec)).copiedFrom(cc)

          case cc @ CaseClassSelector(ct, e, sel) =>
            CaseClassSelector(tpeSub(ct).asInstanceOf[CaseClassType], srec(e), sel).copiedFrom(cc)

          case cc @ CaseClassInstanceOf(ct, e) =>
            CaseClassInstanceOf(tpeSub(ct).asInstanceOf[CaseClassType], srec(e)).copiedFrom(cc)

          case l @ Let(id, value, body) =>
            val newId = freshId(id, tpeSub(id.getType))
            Let(newId, srec(value), rec(idsMap + (id -> newId))(body)).copiedFrom(l)

          case c @ Choose(pred, oimpl) =>
            Choose(rec(idsMap)(pred), oimpl.map(srec)).copiedFrom(c)

          case l @ Lambda(args, body) =>
            val newArgs = args.map { arg =>
              val tpe = tpeSub(arg.getType)
              ValDef(freshId(arg.id, tpe))
            }
            val mapping = args.map(_.id) zip newArgs.map(_.id)
            Lambda(newArgs, rec(idsMap ++ mapping)(body)).copiedFrom(l)

          case p @ Passes(in, out, cases) =>
            val (newIn, newCases) = onMatchLike(in, cases)
            passes(newIn, srec(out), newCases).copiedFrom(p)
            
          case m @ MatchExpr(e, cases) =>
            val (newE, newCases) = onMatchLike(e, cases)
            matchExpr(newE, newCases).copiedFrom(m)

          case Error(tpe, desc) =>
            Error(tpeSub(tpe), desc).copiedFrom(e)
          
          case g @ GenericValue(tpar, id) =>
            tpeSub(tpar) match {
              case newTpar : TypeParameter => 
                GenericValue(newTpar, id).copiedFrom(g)
              case other => // FIXME any better ideas?
                sys.error(s"Tried to substitute $tpar with $other within GenericValue $g")
            }
          
          case ens @ Ensuring(body, pred) =>
            Ensuring(srec(body), rec(idsMap)(pred)).copiedFrom(ens)

          case s @ FiniteSet(elements) if elements.isEmpty =>
            val SetType(tp) = s.getType
            EmptySet(tpeSub(tp)).copiedFrom(s)

          case v @ Variable(id) if idsMap contains id =>
            Variable(idsMap(id)).copiedFrom(v)

          case u @ UnaryOperator(e, builder) =>
            builder(srec(e)).copiedFrom(u)

          case b @ BinaryOperator(e1, e2, builder) =>
            builder(srec(e1), srec(e2)).copiedFrom(b)

          case n @ NAryOperator(es, builder) =>
            builder(es.map(srec)).copiedFrom(n)

          case _ =>
            e
        }
      }

      //println("\\\\"*80)
      //println(tps)
      //println(ids.map{ case (k,v) => k.uniqueName+" -> "+v.uniqueName })
      //println("\\\\"*80)
      //println(e)
      val res = rec(ids)(e)
      //println(".."*80)
      //println(res)
      //println("//"*80)
      res
    }
  }
}
