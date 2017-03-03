package leon
package synthesis
package stoch

import leon.purescala.Extractors.Operator
import purescala.Definitions.Program
import purescala.Expressions.Expr
import purescala.{ExprOps, TypeOps}
import purescala.Types.{FunctionType, TypeParameter, TypeTree}

object PCFGStats {

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

  def exprConstrFuncType(e: Expr): FunctionType = {
    val Operator(es, _) = e
    return FunctionType(es.map(_.getType), e.getType)
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

}
