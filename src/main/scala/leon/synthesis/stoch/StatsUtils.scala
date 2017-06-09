package leon
package synthesis
package stoch

import purescala.Extractors.Operator
import purescala.Definitions.{ModuleDef, Program}
import purescala.Expressions._
import purescala.Types._
import purescala.{ExprOps, TypeOps}
import purescala.TypeOps.bestRealType
import Stats._
import leon.utils.Position
import leon.utils.MapUtils.seqToMap

object StatsUtils {

  // All sub-expressions of an expression
  def allSubExprs(expr: Expr): Seq[Expr] = ExprOps.collectPreorder{ List(_) }(expr)

  // All sub-expressions of a program
  def allSubExprs(p: Program): Seq[Expr] = {
    for {
      unit <- p.units if unit.isMainUnit
      f <- unit.definedFunctions
      e <- allSubExprs(f.fullBody)
    } yield e
  }

  def allSubExprs(ctx: LeonContext, p: Program): Seq[Expr] = allSubExprs(p)

  def normalizeExprs(ctx: LeonContext, exprs: Seq[Expr]): Seq[Expr] = {
    def commutative(e: Expr) = e match {
      case _: Plus | _ : Times | _ : BVPlus | _ : BVTimes => true
      case _ => false
    }
    exprs.map {
      case GreaterThan(e1, e2) => LessThan(e2, e1)
      case GreaterEquals(e1, e2) => LessEquals(e2, e1)
      //case e@Operator(Seq(e1, e2), builder)
      //    if commutative(e) && e1.hashCode() < e2.hashCode() =>
      //  // normalize commutative operators by putting operand with larger hashCode first
      //  builder(Seq(e2, e1))
      case other => other
    }
  }

  // All subexressions of a program with (parent, position in parent)
  def allSubExprs2(expr: Expr): Seq[(Expr, Option[(Int, Expr)])] = ExprOps.collectPreorder { (e: Expr) =>
    val Operator(es, _) = e
    es.zipWithIndex.map { case (esi, i) => (esi, Some(i, e)) }
  }(expr) :+ (expr, None)

  def allSubExprs2(p: Program): Seq[(Expr, Option[(Int, Expr)])] = {
    for {
      unit <- p.units
      f <- unit.definedFunctions
      e <- allSubExprs2(f.fullBody)
    } yield e
  }

  // Type normalization
  // We assume that all type parameters are ordered: T, U, V, ...
  // Each type is converted into the lexicographically smallest type where equality / inequality constraints are
  // preserved between all type parameter occurrences.
  // For example:
  // 1. All base types are unchanged: BigInt ~~> BigInt, Unit ~~> Unit, String ~~> String, etc.
  // 2. All types which are individual occurrences of a type parameter are turned into T:
  //    T ~~> T, U ~~> T, V ~~> T, etc.
  // 3. Arrow types, "T -> T" ~~> "T -> T", "U -> U" ~~> "T -> T", and "V -> U" ~~> "T -> U"
  // 4. "U -> BigInt" ~~> "T -> BigInt"

  def getTypeParams(typeTree: TypeTree): Seq[TypeParameter] = {
    TypeOps.collectPreorder{ tt => List(tt) }(typeTree)
           .collect{ case tp: TypeParameter => tp }
           .distinct
  }

  private val freshTypeParams = Stream.continually(TypeParameter.fresh("TP", true))
  def normalizeType(typeTree: TypeTree): TypeTree = {
    val thisParams = getTypeParams(typeTree).distinct
    val renaming = thisParams.zip(freshTypeParams)
                             .map { case (x, y) => (x: TypeTree, y: TypeTree) }
                             .toMap
    val ans = bestRealType(TypeOps.replace(renaming, typeTree))
    ans
  }

  def normalizeTypes(seq: Seq[TypeTree]): Seq[TypeTree] = {
    seq.map(typeTree => normalizeType(typeTree))
  }

  // (operand types) => expr. type
  // All classes have been mapped to the top of hierarchy
  def exprConstrFuncType(e: Expr): FunctionType = {
    val Operator(es, _) = e
    FunctionType(es map (e => bestRealType(e.getType)), bestRealType(e.getType))
  }

  def getTypeStatsPretty(ctx: LeonContext, p: Program): String = {
    val ans = new StringBuilder()
    val stats =
      allSubExprs(p)
        .groupBy(e => bestRealType(e.getType))
        .mapValues(_.size)
        .toList
        .sortBy(-_._2)
    for (typeFreq <- stats) {
      ans.append(s"${typeFreq._1} -> ${typeFreq._2}\n")
    }
    ans.toString()
  }

  // Filter expressions with interesting types

  def isCanaryExpr(expr: Expr): Boolean = expr match {
    case v: Variable if v.id.name.contains("f82c414") => true
    case _ => false
  }

  def getCanaryTypes(module: ModuleDef) = {
    module.definedFunctions.map(fd => normalizeType(fd.returnType))
  }

  def getCanaryMap(exprs: Seq[Expr]) = exprs.collect {
    case v: Variable if v.id.name.contains("f82c414") =>
      v.id.name -> normalizeType(v.getType)
  }.toMap

  def isExcludedExpr(e: Expr) = ExprOps.exists {
    case _: MatchExpr => true
    case _ => false
  }(e)

  def canaryTypeFilter(exprs: Seq[Expr], canaryTypes: Seq[TypeTree]): Seq[Expr] = {
    exprs.filter(expr => isSelectableExpr(expr, canaryTypes))
  }

  def canaryTypeFilter2(exprs: Seq[(Expr, Option[(Int, Expr)])], canaryTypes: Seq[TypeTree]): Seq[(Expr, Option[(Int, Expr)])] = {
    exprs.flatMap {
      case (expr, _) if !isSelectableExpr(expr, canaryTypes) =>
        None
      case (expr, Some((_, par))) if !isSelectableExpr(par, canaryTypes) =>
        Some((expr, None))
      case other =>
        Some(other)
    }
  }

  def isSelectableExpr(
    expr: Expr,
    canaryTypes: Seq[TypeTree]
  ): Boolean = {
    isSelectableType(exprConstrFuncType(expr), canaryTypes, false) && !isExcludedExpr(expr)
  }

  def isSelectableType(tt: TypeTree, canaryTypes: Seq[TypeTree], strict: Boolean): Boolean = {
    canaryTypes.contains(normalizeType(tt)) || (tt match {
      case FunctionType(from, to) if !strict || StatsMain.SELECT_FUNCTION_TYPES =>
        (from :+ to).forall(tt => isSelectableType(tt, canaryTypes, strict))
      case TupleType(bases) if !strict || StatsMain.SELECT_TUPLE_TYPES =>
        bases.forall(tt => isSelectableType(tt, canaryTypes, strict))
      case _ => false
    })
  }

  def groupAndFilterExprs(
    canaryTypes: Seq[TypeTree],
    exprs: Seq[Expr]
  ): ExprConstrStats = {

    val tuples: Seq[(TypeTree, (Class[_ <: Expr], (Seq[TypeTree], Expr)))] = exprs map { expr =>
      val FunctionType(argTypes, resType) = normalizeType(exprConstrFuncType(expr))
      (resType, (expr.getClass, (argTypes, expr)))
    }

    val strictType = {
      (t: TypeTree) => isSelectableType(t, canaryTypes, true)
    }

    seqToMap(tuples).mapValues( perResType =>
      seqToMap(perResType).mapValues( perClass =>
        seqToMap(perClass)
          .mapValues(_.filterNot(isCanaryExpr))
          .filterKeys(_.forall(strictType))
      )
    ).filterKeys(strictType)
  }

  /* // Normalized expression type -> Relation to parent -> Constructor -> ArgType* -> Expr*
  type ECS2 = Map[TypeTree, Map[Option[(Int, Class[_ <: Expr])], Map[Class[_ <: Expr], Map[Seq[TypeTree], Seq[Expr]]]]]
  // Normalized expression type -> Relation to parent -> Position of function definition -> Expression*
  type FCS2 = Map[TypeTree, Map[Option[(Int, Class[_ <: Expr])], Map[Position, Seq[FunctionInvocation]]]]
  // Normalized expression type -> Relation to parent -> Value -> (Literal[_] <: Expr)*
  type LS2 = Map[TypeTree, Map[Option[(Int, Class[_ <: Expr])], Map[Any, Seq[Literal[_]]]]] */

  def groupAndFilterExprs2(
    canaryTypes: Seq[TypeTree],
    exprs: Seq[(Expr, Option[(Int, Expr)])]
  ): ECS2 = {

    def parGroup(idxPar: (Int, Expr)): (Int, Class[_ <: Expr]) = (idxPar._1, idxPar._2.getClass)
    val tuples: Seq[(TypeTree, (Option[(Priority, Class[_ <: Expr])], (Class[_ <: Expr], (Seq[TypeTree], Expr))))] =
      exprs.map { case (e, par) =>
        val FunctionType(argTypes, resType) = normalizeType(exprConstrFuncType(e))
        (resType, (par map parGroup, (e.getClass, (argTypes, e))))
      }

    val strictType = {
      (t: TypeTree) => isSelectableType(t, canaryTypes, true)
    }
    seqToMap(tuples).mapValues( perResType =>
      seqToMap(perResType).mapValues( perParent =>
        seqToMap(perParent).mapValues( perClass =>
          seqToMap(perClass)
            .mapValues(_.filterNot(isCanaryExpr))
            .filterKeys(_.forall(strictType))
        )
      )
    ).filterKeys(strictType)

  }

  def normalizeConstrType(
    canaryTypes: Map[String, TypeTree],
    canaryInsts: Seq[Variable],
    expr: Expr
  ): FunctionType = {
    var constrType = normalizeType(exprConstrFuncType(expr)).asInstanceOf[FunctionType]
    val classTypes = TypeOps.collectPreorder(tt => Seq(tt))(constrType)
                            .collect{ case ct: ClassType => ct }
    for (ct <- classTypes) {
      val ctCanaryInst = canaryInsts.find { v =>
        v.getType match {
          case vt: ClassType => vt.classDef == ct.classDef
          case _ => false
        }
      }.get
      val ctCanary = canaryTypes(ctCanaryInst.id.name).asInstanceOf[ClassType]
      val map: Map[TypeTree, TypeTree] = ctCanary.tps.zip(ct.tps).toMap
      val map2: Map[TypeTree, TypeTree] = Map(ct -> TypeOps.replace(map, ctCanary))
      constrType = TypeOps.replace(map2, constrType).asInstanceOf[FunctionType]
    }
    constrType
  }

  def ttStatsToFCS(ttStats: Map[Class[_ <: Expr], Map[Seq[TypeTree], Seq[Expr]]]): Map[Position, Seq[FunctionInvocation]] = {
    ttStats.values.flatMap(_.values).flatten
      .collect { case fi: FunctionInvocation => fi }
      .groupBy(_.tfd.getPos)
      .mapValues(_.toSeq)
  }

  def getFunctionCallStats(ecs: ExprConstrStats): FunctionCallStats = {
    ecs.mapValues(ttStatsToFCS)
  }

  /* // Normalized expression type -> Relation to parent -> Constructor -> ArgType* -> Expr*
  type ECS2 = Map[TypeTree, Map[Option[(Int, Class[_ <: Expr])], Map[Class[_ <: Expr], Map[Seq[TypeTree], Seq[Expr]]]]]
  // Normalized expression type -> Relation to parent -> Position of function definition -> Expression*
  type FCS2 = Map[TypeTree, Map[Option[(Int, Class[_ <: Expr])], Map[Position, Seq[FunctionInvocation]]]]
  // Normalized expression type -> Relation to parent -> Value -> (Literal[_] <: Expr)*
  type LS2 = Map[TypeTree, Map[Option[(Int, Class[_ <: Expr])], Map[Any, Seq[Literal[_]]]]] */

  def getFCS2(ecs2: ECS2): FCS2 = {
    ecs2.mapValues(_.mapValues(ttStatsToFCS))
  }

  def ttStatsToLitStats(ttStats: Map[Class[_ <: Expr], Map[Seq[TypeTree], Seq[Expr]]]): Map[Any, Seq[Literal[_]]] = {
    ttStats.values.flatMap(_.values).flatten
      .collect{ case l: Literal[_] => l }
      .groupBy(_.value)
      .mapValues(_.toSeq)
  }

  def getLitStats(ecs: ExprConstrStats): LitStats = {
    ecs.mapValues(ttStatsToLitStats)
  }

  def getLS2(ecs2: ECS2): LS2 = {
    ecs2.mapValues(_.mapValues(ttStatsToLitStats))
  }

  def replaceKnownNames(s: String) =
    s.replaceAll("variable\\$\\d*", "variable")
     .replaceAll("List\\$\\d*", "List")
     .replaceAll("Cons\\$\\d*", "Cons")
     .replaceAll("Nil\\$\\d*", "Nil")
     .replaceAll("Option\\$\\d*", "Option")
     .replaceAll("Some\\$\\d*", "Some")
     .replaceAll("None\\$\\d*", "None")
     .replaceAll("case class (.*?)\\(", "implicit class $1(val ")

}
