package leon
package synthesis
package stoch

import purescala.Extractors.Operator
import purescala.Definitions.Program
import purescala.Expressions._
import purescala.Types._
import purescala.{ExprOps, TypeOps}
import purescala.TypeOps.bestRealType
import Stats._
import leon.utils.Position

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

  def normalizeExprs(ctx: LeonContext, exprs: Seq[Expr]): Seq[Expr] = exprs.map {
    case GreaterThan(e1, e2) => LessThan(e2, e1)
    case GreaterEquals(e1, e2) => LessEquals(e2, e1)
    case e => e
  }

  // All subexressions of a program with (parent, position in parent)
  def allSubExprs2(expr: Expr): Seq[(Expr, Option[(Int, Expr)])] = ExprOps.collectPreorder { (e: Expr) =>
    val Operator(es, _) = e
    es.zipWithIndex.map { case (esi, i) => (esi, Some(i, e)) }
  }(expr) :+ (expr, None)

  def allSubExprs2(p: Program): Seq[(Expr, Option[(Int, Expr)])] = {
    for {
      unit <- p.units if unit.isMainUnit
      f <- unit.definedFunctions
      e <- allSubExprs2(f.fullBody)
    } yield e
  }

  def allSubExprs2(ctx: LeonContext, p: Program): Seq[(Expr, Option[(Int, Expr)])] = allSubExprs2(p)

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

  private val freshTypeParams = Stream.continually(TypeParameter.fresh("T", true))
  def normalizeType(typeTree: TypeTree): TypeTree = {
    val thisParams = getTypeParams(typeTree).distinct
    val renaming = thisParams.zip(freshTypeParams)
                             .map { case (x, y) => (x.asInstanceOf[TypeTree], y.asInstanceOf[TypeTree]) }
                             .toMap
    val ans = TypeOps.replace(renaming, typeTree)
    // println(s"Normalizing ${typeTree}: ${ans}")
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

  def getCanaryExprs(exprs: Seq[Expr]): Seq[Variable] = {
    exprs.collect { case v: Variable if v.id.name.contains("f82c414") => v }
  }

  def isExcludedExpr(e: Expr) = ExprOps.exists {
    case _: MatchExpr => true
    case _ => false
  }(e)

  def canaryTypeFilter(exprs: Seq[Expr]): Seq[Expr] = {
    val canaryExprs = getCanaryExprs(exprs)
    val canaryTypes = canaryExprs.map(_.getType).map(tt => normalizeType(tt))
    exprs.filter(expr => isSelectableExpr(expr, canaryTypes))
  }

  def canaryTypeFilter2(exprs: Seq[(Expr, Option[(Int, Expr)])]): Seq[(Expr, Option[(Int, Expr)])] = {
    val canaryExprs = getCanaryExprs(exprs.map(_._1))
    val canaryTypes = canaryExprs.map(_.getType).map(tt => normalizeType(tt))

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
    isSelectableType(exprConstrFuncType(expr), canaryTypes) && !isExcludedExpr(expr)
  }

  def isSelectableType(tt: TypeTree, canaryTypes: Seq[TypeTree]): Boolean = {
    canaryTypes.contains(normalizeType(tt)) || (tt match {
      case FunctionType(from, to) => (from :+ to).forall(tt => isSelectableType(tt, canaryTypes))
      case TupleType(bases) => bases.forall(tt => isSelectableType(tt, canaryTypes))
      case _ => false
    })
  }

  def isSelectableTypeStrict(tt: TypeTree, canaryTypes: Seq[TypeTree]): Boolean = {
    canaryTypes.contains(normalizeType(tt)) || (tt match {
      case FunctionType(from, to) if StatsMain.SELECT_FUNCTION_TYPES =>
        (from :+ to).forall(tt => isSelectableTypeStrict(tt, canaryTypes))
      case TupleType(bases) if StatsMain.SELECT_TUPLE_TYPES =>
        bases.forall(tt => isSelectableTypeStrict(tt, canaryTypes))
      case _ => false
    })
  }

  def groupExprs(
    fileName: String,
    canaryTypes: Map[String, TypeTree],
    exprs: Seq[Expr]
  ): ExprConstrStats = {
    val canaryInsts = exprs.collect{ case v: Variable if canaryTypes.contains(v.id.name) => v }
    require(canaryTypes.keys.forall(v => canaryInsts.exists(_.id.name == v)))

    exprs.map(expr => (expr, normalizeConstrType(canaryTypes, canaryInsts, expr)))
         .groupBy(_._2.to)
         .mapValues(_.groupBy(_._1.getClass))
         .mapValues(_.mapValues(_.groupBy(_._2.from)))
         .mapValues(_.mapValues(_.mapValues(_.map(_._1))))
  }

  /* // Normalized expression type -> Relation to parent -> Constructor -> ArgType* -> Expr*
  type ECS2 = Map[TypeTree, Map[Option[(Int, Class[_ <: Expr])], Map[Class[_ <: Expr], Map[Seq[TypeTree], Seq[Expr]]]]]
  // Normalized expression type -> Relation to parent -> Position of function definition -> Expression*
  type FCS2 = Map[TypeTree, Map[Option[(Int, Class[_ <: Expr])], Map[Position, Seq[FunctionInvocation]]]]
  // Normalized expression type -> Relation to parent -> Value -> (Literal[_] <: Expr)*
  type LS2 = Map[TypeTree, Map[Option[(Int, Class[_ <: Expr])], Map[Any, Seq[Literal[_]]]]] */

  def groupExprs2(
    fileName: String,
    canaryTypes: Map[String, TypeTree],
    exprs: Seq[(Expr, Option[(Int, Expr)])]
  ): ECS2 = {
    val canaryInsts = exprs.collect {
      case (v: Variable, _) if canaryTypes.contains(v.id.name) => v
    }
    for (id <- canaryTypes.keys) {
      if (!canaryInsts.exists(_.id.name == id)) {
        val selectableType = isSelectableType(canaryTypes(id), canaryTypes.values.toSeq)
        println(s"Unidentified canary instance in file $fileName! id: $id selectableType: $selectableType")
      }
    }
    require(canaryTypes.keys.forall(v => canaryInsts.exists(_.id.name == v)))

    def parGroup(idxPar: (Int, Expr)): (Int, Class[_ <: Expr]) = (idxPar._1, idxPar._2.getClass)

    exprs.map { case (e, par) => (e, par, normalizeConstrType(canaryTypes, canaryInsts, e)) }
         .groupBy(_._3.to)
         .mapValues(_.groupBy(_._2.map(parGroup)))
         .mapValues(_.mapValues(_.groupBy(_._1.getClass)))
         .mapValues(_.mapValues(_.mapValues(_.groupBy(_._3.from))))
         .mapValues(_.mapValues(_.mapValues(_.mapValues(_.map(_._1)))))
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
