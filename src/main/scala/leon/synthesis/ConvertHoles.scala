/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

import purescala.Common._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Definitions._
import purescala.Constructors._

object ConvertHoles extends LeonPhase[Program, Program] {
  val name        = "Convert Holes to Choose"
  val description = "Convert Holes found in bodies to equivalent Choose"

  /**
   * This phase converts a body with "withOracle{ .. }" into a choose construct:
   *
   * def foo(a: T) = {
   *   require(..a..)
   *   expr(a, ???)
   * } ensuring { x => post(x) }
   *
   * gets converted into:
   *
   * def foo(a: T) {
   *   require(..a..)
   *   val h = choose { (h) => {
   *     val res = expr(a, ???)
   *     post(res)
   *   }
   *   expr(a, h)
   * } ensuring { res =>
   *   post(res)
   * }
   *
   */
  def run(ctx: LeonContext)(pgm: Program): Program = {

    pgm.definedFunctions.foreach(fd => {
      if (fd.hasBody) {

        var holes  = List[Identifier]()

        val newBody = preMap {
          case h @ Hole(tpe, es) =>
            val (expr, ids) = toExpr(h)

            holes ++= ids

            Some(expr)
          case _ =>
            None
        }(fd.body.get)

        if (holes.nonEmpty) {
          val cids = holes.map(_.freshen)
          val pred = fd.postcondition match {
            case Some((id, post)) =>
              replaceFromIDs((holes zip cids.map(_.toVariable)).toMap, Let(id, newBody, post))
            case None =>
              BooleanLiteral(true)
          }

          val withChoose = letTuple(holes, Choose(cids, pred), newBody)

          fd.body = Some(withChoose)
        }

      }

      // Ensure that holes are not found in pre and/or post conditions
      fd.precondition.foreach {
        preTraversal{
          case _: Hole =>
            ctx.reporter.error("Holes are not supported in preconditions. (function "+fd.id.asString(ctx)+")")
          case _ =>
        }
      }

      fd.postcondition.foreach { case (id, post) =>
        preTraversal{
          case _: Hole =>
            ctx.reporter.error("Holes are not supported in postconditions. (function "+fd.id.asString(ctx)+")")
          case _ =>
        }(post)
      }

    })

    pgm
  }

  def toExpr(h: Hole): (Expr, List[Identifier]) = {
    h.alts match {
      case Seq() =>
        val h1 = FreshIdentifier("hole", true).setType(h.getType)
        (h1.toVariable, List(h1))

      case Seq(v) =>
        val h1 = FreshIdentifier("hole", true).setType(BooleanType)
        val h2 = FreshIdentifier("hole", true).setType(h.getType)
        (IfExpr(h1.toVariable, h2.toVariable, v), List(h1, h2))

      case exs =>
        var ids: List[Identifier] = Nil
        val ex = exs.init.foldRight(exs.last)({ (e: Expr, r: Expr) =>
          val h = FreshIdentifier("hole", true).setType(BooleanType)
          ids ::= h
          IfExpr(h.toVariable, e, r)
        })

        (ex, ids.reverse)
    }
  }
}
