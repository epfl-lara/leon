package leon
package synthesis
package stoch

import leon.purescala.Extractors.Operator
import leon.synthesis.stoch.Stats.ExprConstrStats
import purescala.Definitions.Program
import purescala.Expressions.{Expr, Variable}
import purescala.{ExprOps, TypeOps}
import purescala.Types.{ClassType, FunctionType, TypeParameter, TypeTree}

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

  def allSubExprsByType(p: Program): Map[TypeTree, Seq[Expr]] = {
    val ase = allSubExprs(p)
    val allTypeParams = ase.map(_.getType).flatMap(getTypeParams).distinct
    ase.groupBy(expr => normalizeType(allTypeParams, expr.getType))
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
    tt match {
      case FunctionType(from, to) => (from :+ to).forall(tt => isSelectableType(tt, canaryTypes, allTypeParams))
      case _ => canaryTypes.contains(normalizeType(allTypeParams, tt))
    }
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

}
