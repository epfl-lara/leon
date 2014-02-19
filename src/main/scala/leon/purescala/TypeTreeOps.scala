package leon
package purescala

import TreeOps.postMap
import TypeTrees._
import Definitions._
import Common._
import Trees._
import Extractors._

object TypeTreeOps {
  def canBeSubtypeOf(tpe: TypeTree, freeParams: Seq[TypeParameterDef], stpe: TypeTree): Option[Seq[TypeParameter]] = {
    if (freeParams.isEmpty) {
      if (isSubtypeOf(tpe, stpe)) {
        Some(Nil)
      } else {
        None
      }
    } else {
      // TODO
      None
    }
  }

  def bestRealType(t: TypeTree) : TypeTree = t match {
    case c: ClassType if c.classDef.isInstanceOf[CaseClassDef] => {
      c.classDef.parent match {
        case None => CaseClassType(c.classDef.asInstanceOf[CaseClassDef], c.tps)
        case Some(p) => instantiateType(p, (c.classDef.tparams zip c.tps).toMap)
      }
    }
    case other => other
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
    case (o1, o2) if (o1 == o2) => Some(o1)
    case (o1,BottomType) => Some(o1)
    case (BottomType,o2) => Some(o2)
    case (o1,AnyType) => Some(AnyType)
    case (AnyType,o2) => Some(AnyType)

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
          FreshIdentifier(id.name, true).setType(newTpe).copiedFrom(id)
        }

        // Simple rec without affecting map
        val srec = rec(idsMap) _

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

          case m @ MatchExpr(e, cases) =>
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
            }

            MatchExpr(srec(e), cases.map(trCase)).copiedFrom(m)

          case Error(desc) =>
            Error(desc).setType(tpeSub(e.getType)).copiedFrom(e)

          case s @ FiniteSet(elements) if elements.isEmpty =>
            FiniteSet(Nil).setType(tpeSub(s.getType)).copiedFrom(s)

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
