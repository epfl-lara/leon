/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package purescala

object TypeTreeOps {
  import Common._
  import Definitions._
  import TypeTrees._
  import Trees._
  import TreeOps._
  import Extractors._

  def collectParametricTypes(tpe: TypeTree): Set[Identifier] = tpe match {
    case AbstractClassType(_, tparams) => tparams.flatMap(collectParametricTypes(_)).toSet
    case CaseClassType(_, tparams) => tparams.flatMap(collectParametricTypes(_)).toSet
    case TupleType(tpes) => tpes.flatMap(collectParametricTypes(_)).toSet
    case FunctionType(args, ret) => args.flatMap(collectParametricTypes(_)).toSet ++ collectParametricTypes(ret)
    case TypeParameter(id) => Set(id)
    case ArrayType(base) => collectParametricTypes(base)
    case ListType(base) => collectParametricTypes(base)
    case SetType(base) => collectParametricTypes(base)
    case MultisetType(base) => collectParametricTypes(base)
    case MapType(from, to) => collectParametricTypes(from) ++ collectParametricTypes(to)
    case Untyped | AnyType | BottomType | BooleanType | Int32Type | UnitType => Set()
    case _ => scala.sys.error("Unexpected type: " + tpe + " [" + tpe.getClass + "]")
  }

  def collectParametricTypes(expr: Expr): Set[Identifier] = {
    foldRight[Set[Identifier]]({ (e, subs)  =>
      (collectParametricTypes(e.getType) +: subs).toSet.flatten
    })(expr)
  }

  def collectParametricMapping(param: TypeTree, real: TypeTree): Seq[(TypeParameter,TypeTree)] = {
    def rec(tp1: TypeTree, tp2: TypeTree): Seq[(TypeParameter, TypeTree)] = (tp1, tp2) match {
      case (tp1, tp2) if tp1 == tp2 => Seq()
      case (CaseClassType(cd1, tp1), CaseClassType(cd2, tp2)) =>
        if (cd1 == cd2) (tp1 zip tp2).flatMap(p => rec(p._1, p._2))
        else scala.sys.error("Unexpected type combination: " + param + " -> " + real)
      case (AbstractClassType(cd1, tp1), AbstractClassType(cd2, tp2)) =>
        if (cd1 == cd2) (tp1 zip tp2).flatMap(p => rec(p._1, p._2))
        else scala.sys.error("Unexpected type combination: " + param + " -> " + real)
      case (ct1 : ClassType, ct2 : ClassType) =>
        def maybeParent(ct: ClassType): AbstractClassType = ct match {
          case cct @ CaseClassType(_, _) => cct.parent.getOrElse(scala.sys.error("Unexpected type combination: " + param + " -> " + real))
          case act @ AbstractClassType(_, _) => act
        }
        val (act1, act2) = (maybeParent(ct1), maybeParent(ct2))
        rec(act1, act2)
      case (FunctionType(args1, ret1), FunctionType(args2, ret2)) =>
        ((args1 :+ ret1) zip (args2 :+ ret2)).flatMap(p => rec(p._1, p._2))
      case (TupleType(tp1), TupleType(tp2)) =>
        (tp1 zip tp2).flatMap(p => rec(p._1, p._2))
      case (tp @ TypeParameter(id), realType) => Seq(tp -> realType)
      case (ArrayType(base1), ArrayType(base2)) => rec(base1, base2)
      case (ListType(base1), ListType(base2)) => rec(base1, base2)
      case (SetType(base1), SetType(base2)) => rec(base1, base2)
      case (MultisetType(base1), MultisetType(base2)) => rec(base1, base2)
      case (MapType(from1, to1), MapType(from2, to2)) => rec(from1, from2) ++ rec(to1, to2)
      case _ => scala.sys.error("Unexpected type combination: " + param + " -> " + real)
    }

    rec(param, real)
  }

  def mergeParametricMapping(pairs: Seq[(TypeParameter,TypeTree)]): Option[Map[TypeParameter,TypeTree]] = {
    pairs.foldLeft[Option[Map[TypeParameter,TypeTree]]](Some(Map())) { case (opt, (tp,tpe)) =>
      opt.map(map => if (!map.contains(tp)) Some(map + (tp -> tpe)) else leastUpperBound(map(tp), tpe).map(t => map + (tp -> t))).flatten
    }
  }

  def transitiveRoots(expr: Expr): Seq[ClassType] = {
    transitiveTypes(expr).toSeq.collect {
      case (cct : CaseClassType) if !cct.classDef.hasParent => cct
      case (act : AbstractClassType) if act.knownChildren.filter(_.isInstanceOf[CaseClassType]).nonEmpty => act
    }
  }

  def transitiveTypes(expr: Expr): Set[TypeTree] = {
    import scala.collection.mutable.{Set => MutableSet}

    val functions : MutableSet[TypedFunDef] = MutableSet.empty

    val baseTypes : Set[TypeTree] = {
      import purescala.Extractors._
      def rec(expr: Expr): Set[TypeTree] = Set(expr.getType) ++ (expr match {
        case fi @ FunctionInvocation(fd, args) =>
          val tfd = TypedFunDef(fd, fi.tparams)
          args.flatMap(rec(_)).toSet ++ (if (functions(tfd)) Set() else {
            functions += tfd
            tfd.precondition.map(rec(_)).toSet.flatten ++
              tfd.body.map(rec(_)).toSet.flatten ++
              tfd.postcondition.map(p => rec(p._2)).toSet.flatten
          })
        case NAryOperator(args, _) => args.flatMap(rec(_)).toSet
        case BinaryOperator(e1, e2, _) => rec(e1) ++ rec(e2)
        case UnaryOperator(e, _) => rec(e)
        case _ => Set.empty
      })

      rec(expr)
    }

    def expandTypes(tpe: TypeTree): Seq[TypeTree] = {
      val seen : MutableSet[TypeTree] = MutableSet()
      def rec(tpe: TypeTree): Set[TypeTree] = if (seen(tpe)) Set() else {
        seen += tpe
        Set(tpe) ++ (tpe match {
          case SetType(tpe) => rec(tpe)
          case ListType(tpe) => rec(tpe)
          case ArrayType(tpe) => rec(tpe)
          case MultisetType(tpe) => rec(tpe)
          case MapType(from, to) => rec(from) ++ rec(to)
          case TupleType(argTypes) => argTypes.flatMap(rec(_)).toSet
          case FunctionType(argTypes, retType) => argTypes.flatMap(rec(_)).toSet ++ rec(retType)
          case act @ AbstractClassType(_, tparams) =>
            tparams.flatMap(rec(_)).toSet ++ act.knownChildren.flatMap(rec(_))
          case cct @ CaseClassType(_, tparams) =>
            tparams.flatMap(rec(_)).toSet ++ cct.fields.flatMap(f => rec(f.tpe)) ++ cct.parent.toSeq.flatMap(rec(_))
          case _: TypeParameter | Untyped | AnyType | BottomType | BooleanType | Int32Type | UnitType => Set()
        })
      }
      rec(tpe).toSeq
    }

    baseTypes.flatMap(expandTypes(_)).toSet
  }

  def collectType[T](tpe: TypeTree, matcher: PartialFunction[TypeTree,T]): Set[T] = {
    def recSeq(tpes: Seq[TypeTree]): Set[T] = tpes.foldLeft(Set[T]())((acc, tpe) => acc ++ rec(tpe))

    def rec(tpe: TypeTree): Set[T] = (if (matcher.isDefinedAt(tpe)) Set(matcher(tpe)) else Set()) ++ (tpe match {
      case AbstractClassType(cd, tparams) => recSeq(tparams)
      case CaseClassType(cd, tparams) => recSeq(tparams)
      case TupleType(tpes) => recSeq(tpes)
      case FunctionType(args, ret) => recSeq(args) ++ rec(ret)
      case ArrayType(base) => rec(base)
      case ListType(base) => rec(base)
      case SetType(base) => rec(base)
      case MultisetType(base) => rec(base)
      case MapType(from, to) => rec(from) ++ rec(to)
      case _: TypeParameter | Untyped | AnyType | BottomType | BooleanType | Int32Type | UnitType => Set()
      case _ => scala.sys.error("Unexpected type: " + tpe + " [" + tpe.getClass + "]")
    })

    rec(tpe)
  }

  def containsGenericity(expr: Expr): Boolean = exists { e =>
    (containsType(e.getType, _.isInstanceOf[TypeParameter])) || (e match {
      case FunctionInvocation(fd, _) => fd.tparams.nonEmpty
      case CaseClass(cct, _) => cct.tparams.nonEmpty
      case _ => false
    })
  }(expr)

  def containsType(tpe: TypeTree, matcher: TypeTree => Boolean): Boolean = {
    collectType(tpe, { case typeTree if matcher(typeTree) => typeTree }).nonEmpty
  }

  def searchAndReplaceTypesDFS(subst: TypeTree => Option[TypeTree])(tpe: TypeTree): TypeTree = {
    def rec(tpe: TypeTree): TypeTree = {
      val replaced = tpe match {
        case AbstractClassType(cd, tparams) => AbstractClassType(cd, tparams.map(rec(_)))
        case CaseClassType(cd, tparams) => CaseClassType(cd, tparams.map(rec(_)))
        case TupleType(tpes) => TupleType(tpes.map(rec(_)))
        case FunctionType(args, ret) => FunctionType(args.map(rec(_)), rec(ret))
        case ArrayType(base) => ArrayType(rec(base))
        case ListType(base) => ListType(rec(base))
        case SetType(base) => SetType(rec(base))
        case MultisetType(base) => MultisetType(rec(base))
        case MapType(from, to) => MapType(rec(from), rec(to))
        case _: TypeParameter | Untyped | AnyType | BottomType | BooleanType | Int32Type | UnitType => tpe
        case _ => scala.sys.error("Unexpected type: " + tpe + " [" + tpe.getClass + "]")
      }

      subst(replaced) match {
        case Some(newTpe) => newTpe
        case None => if (replaced == tpe) tpe else replaced
      }
    }

    rec(tpe)
  }

  def replaceTypesFromTPs(subst: TypeParameter => Option[TypeTree], tpe: TypeTree, recursive: Boolean = false) = {
    def rec(tpe: TypeTree): TypeTree = tpe match {
      case (tp: TypeParameter) => subst(tp) match {
        case Some(newType) => if (recursive && newType != tpe) rec(newType) else newType
        case None => tpe
      }
      case AbstractClassType(cd, tparams) => AbstractClassType(cd, tparams.map(rec(_)))
      case CaseClassType(cd, tparams) => CaseClassType(cd, tparams.map(rec(_)))
      case TupleType(tpes) => TupleType(tpes.map(rec(_)))
      case FunctionType(args, ret) => FunctionType(args.map(rec(_)), rec(ret))
      case ArrayType(base) => ArrayType(rec(base))
      case ListType(base) => ListType(rec(base))
      case SetType(base) => SetType(rec(base))
      case MultisetType(base) => MultisetType(rec(base))
      case MapType(from, to) => MapType(rec(from), rec(to))
      case Untyped | AnyType | BottomType | BooleanType | Int32Type | UnitType => tpe
      case _ => scala.sys.error("Unexpected type: " + tpe + " [" + tpe.getClass + "]")
    }

    rec(tpe)
  }

  def replaceTypesInExpr(tpeSubst: Map[TypeParameter, TypeTree], idSubst: Map[Identifier, Expr], expr: Expr): Expr = {
    replaceTypesInExpr(tpeSubst.get _, idSubst, expr)
  }

  def replaceTypesInExpr(subst: TypeParameter => Option[TypeTree], idSubst: Map[Identifier, Expr], expr: Expr): Expr = {
    def replaceInPattern(pattern: Pattern): (Pattern, Map[Identifier, Identifier]) = pattern match {
      case InstanceOfPattern(binder, ct) =>
        val newBinder = binder.map(id => id.freshenWithType(replaceTypesFromTPs(subst, id.getType)))
        val newIdMap = binder.map(id => id -> newBinder.get).toMap
        (InstanceOfPattern(newBinder, replaceTypesFromTPs(subst, ct).asInstanceOf[ClassType]), newIdMap)
      case CaseClassPattern(binder, cct, subs) =>
        val newBinder = binder.map(id => id.freshenWithType(replaceTypesFromTPs(subst, id.getType)))
        val newIdMap = binder.map(id => id -> newBinder.get).toMap
        val (newSubs, subsMappings) = subs.map(replaceInPattern(_)).unzip
        (CaseClassPattern(newBinder, replaceTypesFromTPs(subst, cct).asInstanceOf[CaseClassType], newSubs), newIdMap ++ subsMappings.flatten)
      case TuplePattern(binder, subs) =>
        val newBinder = binder.map(id => id.freshenWithType(replaceTypesFromTPs(subst, id.getType)))
        val newIdMap = binder.map(id => id -> newBinder.get).toMap
        val (newSubs, subsMappings) = subs.map(replaceInPattern(_)).unzip
        (TuplePattern(newBinder, newSubs), newIdMap ++ subsMappings.flatten)
      case WildcardPattern(binder) =>
        val newBinder = binder.map(id => id.freshenWithType(replaceTypesFromTPs(subst, id.getType)))
        val newIdMap = binder.map(id => id -> newBinder.get).toMap
        (WildcardPattern(newBinder), newIdMap)
    }

    def rec(expr: Expr, idMap: Map[Identifier, Expr]): Expr = expr match {
      case MatchExpr(e, cases) => MatchExpr(rec(e, idMap), cases.map {
        case SimpleCase(pattern, e) =>
          val (newPattern, patternIdMap) = replaceInPattern(pattern)
          SimpleCase(newPattern, rec(e, idMap ++ patternIdMap.mapValues(_.toVariable)))
        case GuardedCase(pattern, guard, e) =>
          val (newPattern, patternIdMap) = replaceInPattern(pattern)
          val newIdMap = idMap ++ patternIdMap.mapValues(_.toVariable)
          GuardedCase(newPattern, rec(guard, newIdMap), rec(e, newIdMap))
      })
      case CaseClass(cct, args) => CaseClass(replaceTypesFromTPs(subst, cct).asInstanceOf[CaseClassType], args.map(rec(_, idMap)))
      case CaseClassSelector(cct, e, id) => CaseClassSelector(replaceTypesFromTPs(subst, cct).asInstanceOf[CaseClassType], rec(e, idMap), id)
      case CaseClassInstanceOf(cct, e) => CaseClassInstanceOf(replaceTypesFromTPs(subst, cct).asInstanceOf[CaseClassType], rec(e, idMap))
      case AnonymousFunction(args, body) => {
        val newIds = args.map(vd => vd.id.freshenWithType(replaceTypesFromTPs(subst, vd.tpe)))
        val newIdMap = (args.map(_.id) zip newIds).toMap
        val newArgs = newIds.map(id => VarDecl(id, id.getType))
        AnonymousFunction(newArgs, rec(body, idMap ++ newIdMap.mapValues(_.toVariable)))
      }
      case Variable(id) => idMap.getOrElse(id, id.toVariable)
      case NAryOperatorUntyped(es, recons) =>
        val res = recons(es.map(rec(_, idMap)))
        if (res.getType == Untyped) res.setType(replaceTypesFromTPs(subst, expr.getType)) else res
      case BinaryOperatorUntyped(e1, e2, recons) =>
        val res = recons(rec(e1, idMap), rec(e2, idMap))
        if (res.getType == Untyped) res.setType(replaceTypesFromTPs(subst, expr.getType)) else res
      case UnaryOperatorUntyped(e, recons) =>
        val res = recons(rec(e, idMap))
        if (res.getType == Untyped) res.setType(replaceTypesFromTPs(subst, expr.getType)) else res
      case (t : Terminal) => t
      case _ => scala.sys.error("Unexpected expr " + expr + " [" + expr.getClass + "]")
    }

    rec(expr, idSubst)
  }

  def alignTypes(e1: Expr, e2: Expr): (Expr, Expr) = {
    def rec(tp1: TypeTree, tp2: TypeTree): Option[(TypeTree, TypeTree)] = (tp1, tp2) match {
      case (c1: ClassType, c2: ClassType) =>
        var c: ClassType = c1
        var reducer: ClassType => ClassType = ct => ct
        var mapping: Map[ClassTypeDef, (ClassType, ClassType => ClassType)] = Map(c.classDef -> (c -> reducer))

        while (c.parent.isDefined) {
          val classDef = c.classDef
          val parent = c.parent.get
          val lastReducer = reducer
          reducer = ct => lastReducer(ct.asInstanceOf[AbstractClassType].knownChildren.find(_.id == classDef.id).get)
          mapping += parent.classDef -> (parent -> reducer)
          c = parent
        }

        c = c2
        reducer = ct => ct
        var found = if (mapping.contains(c.classDef)) {
          Some(mapping(c.classDef) -> (c -> reducer))
        } else {
          None
        }

        while (found.isEmpty && c.parent.isDefined) {
          val classDef = c.classDef
          val parent = c.parent.get
          val lastReducer = reducer
          reducer = ct => lastReducer(ct.asInstanceOf[AbstractClassType].knownChildren.find(_.id == classDef.id).get)
          if (mapping.contains(parent.classDef)) found = Some(mapping(parent.classDef) -> (parent -> reducer))
          c = parent
        }

        found.map { case ((c1, reducer1), (c2, reducer2)) =>
          assert(c1.classDef == c2.classDef)
          val otparams = (c1.tparams zip c2.tparams).map(p => rec(p._1, p._2))
          if (otparams.exists(!_.isDefined)) None else {
            val (tparams1, tparams2) = otparams.map(_.get).unzip
            val ct1 = classDefToClassType(c1.classDef, tparams1)
            val ct2 = classDefToClassType(c2.classDef, tparams2)
            Some(reducer1(ct1) -> reducer2(ct2))
          }
        }.flatten
      case (TupleType(args1), TupleType(args2)) =>
        val oargs = (args1 zip args2).map(p => rec(p._1, p._2))
        if (oargs.exists(!_.isDefined)) None else {
          val (nargs1, nargs2) = oargs.map(_.get).unzip
          Some(TupleType(nargs1) -> TupleType(nargs2))
        }
      case (o1, o2) if o1 == o2 => Some(o1 -> o2)
      case (o1, Untyped) => Some(o1 -> o1)
      case (Untyped, o2) => Some(o2 -> o2)
      case (o1, BottomType) => Some(o1 -> o1)
      case (BottomType, o2) => Some(o2 -> o2)
//      FIXME: what should we do with AnyType??
//      case (o1, AnyType) => ??
//      case (AnyType, o2) => ??
      case (FunctionType(args1, ret1), FunctionType(args2, ret2)) =>
        val oargs = (args1 zip args2).map(p => rec(p._1, p._2))
        val oret = rec(ret1, ret2)
        if (oargs.exists(!_.isDefined) || !oret.isDefined) None else {
          val (nargs1, nargs2) = oargs.map(_.get).unzip
          val (nret1, nret2) = oret.get
          Some(FunctionType(nargs1, nret1) -> FunctionType(nargs2, nret2))
        }
      case (MapType(from1, to1), MapType(from2, to2)) => rec(from1, from2).map { case (nfrom1, nfrom2) =>
        rec(to1, to2).map { case (nto1, nto2) => MapType(nfrom1, nto1) -> MapType(nfrom2, nto2) }
      }.flatten
      case (ArrayType(base1), ArrayType(base2)) => rec(base1, base2).map(p => ArrayType(p._1) -> ArrayType(p._2))
      case (ListType(base1), ListType(base2)) => rec(base1, base2).map(p => ListType(p._1) -> ListType(p._2))
      case (SetType(base1), SetType(base2)) => rec(base1, base2).map(p => SetType(p._1) -> SetType(p._2))
      case (MultisetType(base1), MultisetType(base2)) => rec(base1, base2).map(p => MultisetType(p._1) -> MultisetType(p._2))
      case _ => None
    }

    def recons(expr: Expr, tpe: TypeTree): Expr = ((expr, tpe) match {
      case (CaseClass(tp, args), cct: CaseClassType) => CaseClass(cct, (args zip cct.fields).map(p => recons(p._1, p._2.tpe)))
      case (Tuple(args), TupleType(argTypes)) => Tuple((args zip argTypes).map(p => recons(p._1, p._2)))
      case (FiniteMap(singletons), MapType(from, to)) => FiniteMap(singletons.map(p => recons(p._1, from) -> recons(p._2, to)))
      case (FiniteArray(exprs), ArrayType(base)) => FiniteArray(exprs.map(e => recons(e, base)))
      case (FiniteSet(elements), SetType(base)) => FiniteSet(elements.map(e => recons(e, base)))
      case (FiniteMultiset(elements), MultisetType(base)) => FiniteMultiset(elements.map(e => recons(e, base)))
      case _ => expr
    }).setType(tpe)

    rec(e1.getType, e2.getType).map(p => recons(e1, p._1) -> recons(e2, p._2)).getOrElse(e1 -> e2)
  }
}
