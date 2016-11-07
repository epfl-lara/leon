package leon
package synthesis.stoch

import purescala.Common.Identifier
import purescala.Definitions.{FunDef, Program}
import purescala.Expressions._
import purescala.ExprOps
import purescala.Types.TypeTree

case class DeBruijnStats(v: Variable, scope: List[Expr], f: FunDef, dist: Int, relDist: Double)

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
    } else if (expr.isInstanceOf[MatchExpr]) {
      val scrutineeAncs = ancs.head
      val casesAncs = ancs.tail
      scrutineeAncs ++ casesAncs.flatMap(_.map(_ :+ expr))
    } else {
      ancs.flatten
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

  def getVarDist(v: Variable, scope: List[Expr], f: FunDef, index: Int = 0): Int = scope match {
    case Nil => Int.MaxValue
    case Let(binder, _, _) :: scopePrime => if (binder == v.id) index
                                            else getVarDist(v, scopePrime, f, index + 1)
    case LetDef(fds, _) :: scopePrime => if (fds.exists(_.id == v.id)) index
                                         else getVarDist(v, scopePrime, f, index + 1)
    case Forall(args, _) :: scopePrime => if (args.exists(_.id == v.id)) index
                                          else getVarDist(v, scopePrime, f, index + 1)
    case Lambda(args, _) :: scopePrime => if (args.exists(_.id == v.id)) index
                                          else getVarDist(v, scopePrime, f, index + 1)
    case MatchExpr(_, cases) :: scopePrime => if (cases.exists(_.pattern.binders.contains(v.id))) index
                                              else getVarDist(v, scopePrime, f, index + 1)
    case _ => {
      assert(false)
      0
    }
  }

  def getDeBruijnStats(ctx: LeonContext, p: Program): Seq[DeBruijnStats] = {
    for {
      unit <- p.units
      f <- unit.definedFunctions
      scope <- collectVarAncestors(f.fullBody)
      dist = getVarDist(scope._1, scope._2, f)
      relDist = dist.toDouble / scope._2.size
    } yield DeBruijnStats(scope._1, scope._2, f, dist, relDist)
  }

  def getDeBruijnStatsPretty(ctx: LeonContext, p: Program): String = {
    val ans = new StringBuilder()
    for (DeBruijnStats(v, scope, f, dist, relDist) <- getDeBruijnStats(ctx, p)) {
      var pre = ">"
      ans.append(s"${v}\n")
      for (e <- scope) {
        ans.append(s"${pre} ${e}\n")
        pre = pre + ">"
      }
      ans.append(s"${f}\n")
      ans.append(s"Distance: ${dist}\n")
      ans.append(s"Distance: ${relDist}\n")
      ans.append("---\n")
    }
    ans.toString()
  }

}
