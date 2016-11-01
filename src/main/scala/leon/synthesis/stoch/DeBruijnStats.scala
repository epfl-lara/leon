package leon
package synthesis.stoch

import purescala.Common.Identifier
import purescala.Definitions.Program
import purescala.Expressions._
import purescala.ExprOps
import purescala.Types.TypeTree

object DeBruijnStats {

  type Context = List[(Identifier, TypeTree)]

  def collectLeafAncestors(expr: Expr, ancs: Seq[Seq[List[Expr]]]): Seq[List[Expr]] = {
    if (expr.isInstanceOf[Variable]) assert(ancs.isEmpty)

    if (ancs.isEmpty) {
      Seq(List(expr))
    } else if (expr.isInstanceOf[Let] ||
               expr.isInstanceOf[LetDef]) {
      ancs.dropRight(1).flatten ++ ancs.last.map(_ :+ expr)
    } else if (expr.isInstanceOf[Forall] ||
               expr.isInstanceOf[Lambda]) {
      ancs.flatMap(_.map(_ :+ expr))
    } else {
      ancs.flatMap(_.map(_ :+ expr))
    }
  }

  def collectLeafAncestors(expr: Expr): Seq[(Expr, List[Expr])] = {
    val res = ExprOps.fold(collectLeafAncestors)(expr)
    res.map(es => (es.head, es.tail))
  }

  def collectVarAncestors(expr: Expr): Seq[(Variable, List[Expr])] = {
    val leafAncestors = collectLeafAncestors(expr)
    for (ele <- leafAncestors) {
      val leaf = ele._1
      val ancestors = ele._2

      val claim1 = leaf.isInstanceOf[CaseClass] ||
                   leaf.isInstanceOf[Error] ||
                   leaf.isInstanceOf[FiniteBag] ||
                   leaf.isInstanceOf[FiniteMap] ||
                   leaf.isInstanceOf[FiniteSet] ||
                   leaf.isInstanceOf[FunctionInvocation] ||
                   leaf.isInstanceOf[Hole] ||
                   leaf.isInstanceOf[Literal[_]] ||
                   leaf.isInstanceOf[NoTree] ||
                   leaf.isInstanceOf[xlang.Expressions.Old] ||
                   leaf.isInstanceOf[Variable]
      /* if (!claim1) {
        println(s"Unrecognized leaf ${leaf}, with expression type ${ele._1.getClass}")
      } */

      val claim2 = ancestors.forall(!_.isInstanceOf[Variable])
      /* if (!claim2) {
        val variable = ancestors.find(_.isInstanceOf[Variable]).get
        println(s"Mysterious occurrence of variable ${variable} among ancestors of expression ${leaf}.")
        println(s"Ancestors: ${ancestors}")
      } */

      assert(claim1 && claim2)
    }
    leafAncestors.filter(_._1.isInstanceOf[Variable])
                 .map(ele => (ele._1.asInstanceOf[Variable], ele._2))
  }

  def getDeBruijnStats(ctx: LeonContext, p: Program): Seq[(Variable, List[Expr])] = {
    for {
      unit <- p.units
      f <- unit.definedFunctions
      ctx <- collectVarAncestors(f.fullBody)
    } yield ctx
  }

  def getDeBruijnStatsPretty(ctx: LeonContext, p: Program): String = {
    val ans = new StringBuilder()
    for ((v, ctx) <- getDeBruijnStats(ctx, p)) {
      var pre = ">"
      // ans.append(s"${v}\n")
      for (e <- ctx) {
        // ans.append(s"${pre} ${e}\n")
        pre = pre + ">"
      }
      // ans.append("---\n")
    }
    ans.toString()
  }

  def getExprConstrs(ctx: LeonContext, p: Program): Set[Class[_ <: Expr]] = {
    getDeBruijnStats(ctx, p).flatMap(_._2).map(_.getClass).toSet
  }

}
