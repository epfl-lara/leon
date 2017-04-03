package leon
package synthesis
package stoch

import leon.purescala.Extractors.Operator
import leon.synthesis.stoch.Stats._
import leon.utils.Position
import purescala.Definitions.Program
import purescala.Expressions.{Expr, FunctionInvocation, Literal, Variable}
import purescala.{ExprOps, TypeOps}
import purescala.Types._

object StatsUtils {

  // All sub-expressions
  def allSubExprs(expr: Expr): Seq[Expr] = ExprOps.collectPreorder{ e => List(e) }(expr)

  def allSubExprs(p: Program): Seq[Expr] = {
    for {
      unit <- p.units if unit.isMainUnit
      f <- unit.definedFunctions
      e <- allSubExprs(f.fullBody)
    } yield e
  }

  def allSubExprs(ctx: LeonContext, p: Program): Seq[Expr] = allSubExprs(p)

  def allSubExprs2(expr: Expr): Seq[(Expr, Option[(Int, Expr)])] = ExprOps.collectPreorder { (e: Expr) =>
    val Operator(es, op) = e
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
           .filter(_.isInstanceOf[TypeParameter])
           .map(_.asInstanceOf[TypeParameter])
           .distinct
  }

  def normalizeType(allParams: Seq[TypeParameter], typeTree: TypeTree): TypeTree = {
    val thisParams = getTypeParams(typeTree).distinct
    require(thisParams.toSet.subsetOf(allParams.toSet))
    val renaming = thisParams.zip(allParams)
                             .map { case (x, y) => (x.asInstanceOf[TypeTree], y.asInstanceOf[TypeTree]) }
                             .toMap
    val ans = TypeOps.replace(renaming, typeTree)
    // println(s"Normalizing ${typeTree}: ${ans}")
    ans
  }

  def normalizeTypes(seq: Seq[TypeTree]): Seq[TypeTree] = {
    val allParams = seq.flatMap(getTypeParams).distinct
    seq.map(typeTree => normalizeType(allParams, typeTree))
  }

  def exprConstrFuncType(e: Expr): FunctionType = FunctionType(childTypes(e), e.getType)

  def childTypes(e: Expr): Seq[TypeTree] = {
    val Operator(es, _) = e
    es.map(_.getType)
  }

  // Type statistics
  def getTypeStats(ctx: LeonContext, p: Program): Map[TypeTree, Int] = {
    allSubExprs(p).groupBy(_.getType).mapValues(_.size)
  }

  def getTypeStatsPretty(ctx: LeonContext, p: Program): String = {
    val ans = new StringBuilder()
    for (typeFreq <- getTypeStats(ctx, p).toList.sortBy(-_._2)) {
      ans.append(s"${typeFreq._1} -> ${typeFreq._2}\n")
    }
    ans.toString()
  }

  // Filter expressions with interesting types

  def isCanaryExpr(expr: Expr): Boolean = {
    expr.isInstanceOf[Variable] && expr.asInstanceOf[Variable].id.name.contains("f82c414")
  }

  def getCanaryExprs(exprs: Seq[Expr]): Seq[Variable] = {
    exprs.filter(_.isInstanceOf[Variable])
         .map(_.asInstanceOf[Variable])
         .filter(_.id.name.contains("f82c414"))
  }

  def canaryTypeFilter(exprs: Seq[Expr]): Seq[Expr] = {
    val canaryExprs = getCanaryExprs(exprs)
    val allTypeParams = exprs.map(exprConstrFuncType).flatMap(getTypeParams).distinct
    val canaryTypes = canaryExprs.map(_.getType).map(tt => normalizeType(allTypeParams, tt))
    exprs.filter(expr => isSelectableExpr(expr, canaryExprs, canaryTypes, allTypeParams))
  }

  def isSelectableExpr(
                        expr: Expr,
                        canaryExprs: Seq[Expr],
                        canaryTypes: Seq[TypeTree],
                        allTypeParams: Seq[TypeParameter]
                      ): Boolean = {
    isSelectableType(exprConstrFuncType(expr), canaryTypes, allTypeParams)
  }

  def isSelectableType(tt: TypeTree, canaryTypes: Seq[TypeTree], allTypeParams: Seq[TypeParameter]): Boolean = {
    canaryTypes.contains(normalizeType(allTypeParams, tt)) || (tt match {
      case FunctionType(from, to) => (from :+ to).forall(tt => isSelectableType(tt, canaryTypes, allTypeParams))
      case TupleType(bases) => bases.forall(tt => isSelectableType(tt, canaryTypes, allTypeParams))
      case _ => false
    })
  }

  def isSelectableTypeStrict(tt: TypeTree, canaryTypes: Seq[TypeTree], allTypeParams: Seq[TypeParameter]): Boolean = {
    canaryTypes.contains(normalizeType(allTypeParams, tt)) || (tt match {
      case FunctionType(from, to) if StatsMain.SELECT_FUNCTION_TYPES =>
        (from :+ to).forall(tt => isSelectableTypeStrict(tt, canaryTypes, allTypeParams))
      case TupleType(bases) if StatsMain.SELECT_TUPLE_TYPES =>
        bases.forall(tt => isSelectableTypeStrict(tt, canaryTypes, allTypeParams))
      case _ => false
    })
  }

  def groupExprs(
                  allTypeParams: Seq[TypeParameter],
                  canaryTypes: Map[String, TypeTree],
                  exprs: Seq[Expr]
                ): ExprConstrStats = {
    val canaryInsts = exprs.filter(_.isInstanceOf[Variable])
                           .map(_.asInstanceOf[Variable])
                           .filter(v => canaryTypes.contains(v.id.name))
    require(canaryTypes.keys.forall(v => canaryInsts.exists(_.id.name == v)))

    exprs.map(expr => (expr, normalizeConstrType(allTypeParams, canaryTypes, canaryInsts, expr)))
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
                   allTypeParams: Seq[TypeParameter],
                   canaryTypes: Map[String, TypeTree],
                   exprs: Seq[(Expr, Option[(Int, Expr)])]
                 ): ECS2 = {
    val canaryInsts = exprs.filter(_._1.isInstanceOf[Variable])
                           .map { case (e, par) => e.asInstanceOf[Variable] }
                           .filter(v => canaryTypes.contains(v.id.name))
    require(canaryTypes.keys.forall(v => canaryInsts.exists(_.id.name == v)))

    def parGroup(idxPar: (Int, Expr)): (Int, Class[_ <: Expr]) = (idxPar._1, idxPar._2.getClass)

    exprs.map { case(e, par) => (e, par, normalizeConstrType(allTypeParams, canaryTypes, canaryInsts, e)) }
         .groupBy(_._3.to)
         .mapValues(_.groupBy(_._2.map(parGroup)))
         .mapValues(_.mapValues(_.groupBy(_._1.getClass)))
         .mapValues(_.mapValues(_.mapValues(_.groupBy(_._3.from))))
         .mapValues(_.mapValues(_.mapValues(_.mapValues(_.map(_._1)))))
  }

  def normalizeConstrType(
                           allTypeParams: Seq[TypeParameter],
                           canaryTypes: Map[String, TypeTree],
                           canaryInsts: Seq[Variable],
                           expr: Expr
                         ): FunctionType = {
    var constrType = normalizeType(allTypeParams, exprConstrFuncType(expr)).asInstanceOf[FunctionType]
    val classTypes = TypeOps.collectPreorder(tt => Seq(tt))(constrType)
                            .filter(_.isInstanceOf[ClassType])
                            .map(_.asInstanceOf[ClassType])
    for (ct <- classTypes) {
      val ctCanaryInst = canaryInsts.find(v => {
        v.getType.isInstanceOf[ClassType] && v.getType.asInstanceOf[ClassType].classDef == ct.classDef
      }).get
      val ctCanary = canaryTypes(ctCanaryInst.id.name).asInstanceOf[ClassType]
      val map: Map[TypeTree, TypeTree] = ctCanary.tps.zip(ct.tps).toMap
      val map2: Map[TypeTree, TypeTree] = Map(ct -> TypeOps.replace(map, ctCanary))
      constrType = TypeOps.replace(map2, constrType).asInstanceOf[FunctionType]
    }
    constrType
  }

  def ttStatsToFCS(ttStats: Map[Class[_ <: Expr], Map[Seq[TypeTree], Seq[Expr]]]): Map[Position, Seq[FunctionInvocation]] = {
    ttStats.values.flatMap(_.values).flatten
      .filter(_.isInstanceOf[FunctionInvocation])
      .map(_.asInstanceOf[FunctionInvocation])
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
      .filter(_.isInstanceOf[Literal[_]])
      .map(_.asInstanceOf[Literal[_]])
      .groupBy(_.value)
      .mapValues(_.toSeq)
  }

  def getLitStats(ecs: ExprConstrStats): LitStats = {
    ecs.mapValues(ttStatsToLitStats)
  }

  def getLS2(ecs2: ECS2): LS2 = {
    ecs2.mapValues(_.mapValues(ttStatsToLitStats))
  }

}
