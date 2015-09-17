/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import Types._
import Definitions._
import Common._
import Expressions._
import Extractors._
import Constructors._

object TypeOps {
  def typeDepth(t: TypeTree): Int = t match {
    case NAryType(tps, builder) => 1+ (0 +: (tps map typeDepth)).max
  }

  def typeParamsOf(t: TypeTree): Set[TypeParameter] = t match {
    case tp: TypeParameter => Set(tp)
    case _ =>
      val NAryType(subs, _) = t
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
      // TODO: make functions contravariant to arg. types
      if (from1 == from2) {
        leastUpperBound(to1, to2) map { FunctionType(from1, _) }
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
            maps.flatten.toMap
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

            case (up@UnapplyPattern(ob, fd, sps), tp) =>
              val newFd = if ((fd.tps map tpeSub) == fd.tps) fd else fd.fd.typed(fd.tps map tpeSub)
              val newOb = ob.map(id => freshId(id,tp))
              val exType = tpeSub(up.someType.tps.head)
              val exTypes = unwrapTupleType(exType, exType.isInstanceOf[TupleType])
              val (newSps, newMaps) = (sps zip exTypes).map { case (sp, stpe) => trPattern(sp, stpe) }.unzip
              (UnapplyPattern(newOb, newFd, newSps), (ob zip newOb).toMap ++ mapsUnion(newMaps))

            case (WildcardPattern(ob), expTpe) =>
              val newOb = ob.map(id => freshId(id, expTpe))

              (WildcardPattern(newOb), (ob zip newOb).toMap)

            case (LiteralPattern(ob, lit), expType) => 
              val newOb = ob.map(id => freshId(id, expType))
              (LiteralPattern(newOb,lit), (ob zip newOb).toMap)

            case _ =>
              sys.error(s"woot!? $p:$expType")
          }

          (srec(e), cases.map(trCase))//.copiedFrom(m)
        }

        e match {
          case fi @ FunctionInvocation(TypedFunDef(fd, tps), args) =>
            FunctionInvocation(TypedFunDef(fd, tps.map(tpeSub)), args.map(srec)).copiedFrom(fi)

          case mi @ MethodInvocation(r, cd, TypedFunDef(fd, tps), args) =>
            MethodInvocation(srec(r), cd, TypedFunDef(fd, tps.map(tpeSub)), args.map(srec)).copiedFrom(mi)

          case th @ This(ct) =>
            This(tpeSub(ct).asInstanceOf[ClassType]).copiedFrom(th)

          case cc @ CaseClass(ct, args) =>
            CaseClass(tpeSub(ct).asInstanceOf[CaseClassType], args.map(srec)).copiedFrom(cc)

          case cc @ CaseClassSelector(ct, e, sel) =>
            caseClassSelector(tpeSub(ct).asInstanceOf[CaseClassType], srec(e), sel).copiedFrom(cc)

          case cc @ IsInstanceOf(e, ct) =>
            IsInstanceOf(srec(e), tpeSub(ct).asInstanceOf[ClassType]).copiedFrom(cc)

          case cc @ AsInstanceOf(e, ct) =>
            AsInstanceOf(srec(e), tpeSub(ct).asInstanceOf[ClassType]).copiedFrom(cc)

          case l @ Let(id, value, body) =>
            val newId = freshId(id, tpeSub(id.getType))
            Let(newId, srec(value), rec(idsMap + (id -> newId))(body)).copiedFrom(l)

          case l @ Lambda(args, body) =>
            val newArgs = args.map { arg =>
              val tpe = tpeSub(arg.getType)
              ValDef(freshId(arg.id, tpe))
            }
            val mapping = args.map(_.id) zip newArgs.map(_.id)
            Lambda(newArgs, rec(idsMap ++ mapping)(body)).copiedFrom(l)

          case f @ Forall(args, body) =>
            val newArgs = args.map { arg =>
              val tpe = tpeSub(arg.getType)
              ValDef(freshId(arg.id, tpe))
            }
            val mapping = args.map(_.id) zip newArgs.map(_.id)
            Forall(newArgs, rec(idsMap ++ mapping)(body)).copiedFrom(f)

          case p @ Passes(in, out, cases) =>
            val (newIn, newCases) = onMatchLike(in, cases)
            passes(newIn, srec(out), newCases).copiedFrom(p)
            
          case m @ MatchExpr(e, cases) =>
            val (newE, newCases) = onMatchLike(e, cases)
            matchExpr(newE, newCases).copiedFrom(m)

          case Error(tpe, desc) =>
            Error(tpeSub(tpe), desc).copiedFrom(e)
          
          case Hole(tpe, alts) =>
            Hole(tpeSub(tpe), alts.map(srec)).copiedFrom(e)

          case g @ GenericValue(tpar, id) =>
            tpeSub(tpar) match {
              case newTpar : TypeParameter => 
                GenericValue(newTpar, id).copiedFrom(g)
              case other => // FIXME any better ideas?
                sys.error(s"Tried to substitute $tpar with $other within GenericValue $g")
            }

          case s @ FiniteSet(elems, tpe) =>
            FiniteSet(elems.map(srec), tpeSub(tpe)).copiedFrom(s)

          case m @ FiniteMap(elems, from, to) =>
            FiniteMap(elems.map{ case (k, v) => (srec(k), srec(v)) }, tpeSub(from), tpeSub(to)).copiedFrom(m)

          case v @ Variable(id) if idsMap contains id =>
            Variable(idsMap(id)).copiedFrom(v)

          case n @ Operator(es, builder) =>
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
