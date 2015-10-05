/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis

import purescala.Common._
import purescala.Expressions._
import purescala.Types._
import purescala.ExprOps._
import purescala.Definitions._
import purescala.Constructors._

object ConvertHoles extends TransformationPhase {
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

  def convertHoles(e : Expr, ctx : LeonContext) : Expr = {
    val (pre, body, post) = breakDownSpecs(e)

    // Ensure that holes are not found in pre and/or post conditions
    (pre ++ post).foreach {
      preTraversal{
        case h : Hole =>
          ctx.reporter.error("Holes are not supported in preconditions. @"+ h.getPos)
        case _ =>
      }
    }

    body match {
      case Some(body) =>
        var holes  = List[Identifier]()

        val withoutHoles = preMap {
          case h : Hole =>
            val (expr, ids) = toExpr(h)

            holes ++= ids

            Some(expr)
          case _ =>
            None
        }(body)

        if (holes.nonEmpty) {
          val cids: List[Identifier] = holes.map(_.freshen)
          val hToFresh = (holes zip cids.map(_.toVariable)).toMap

          val spec = post match {
            case Some(post: Lambda) =>
              val asLet = letTuple(post.args.map(_.id), withoutHoles, post.body)

              Lambda(cids.map(ValDef(_)), replaceFromIDs(hToFresh, asLet))

            case _ =>
              Lambda(cids.map(ValDef(_)), BooleanLiteral(true))
          }

          val choose = Choose(spec)

          val newBody = if (holes.size == 1) {
            replaceFromIDs(Map(holes.head -> choose), withoutHoles)
          } else {
            letTuple(holes, choose, withoutHoles)
          }

          withPostcondition(withPrecondition(newBody, pre), post)

        } else {
          e
        }

      case None => e
    }
  }


  def apply(ctx: LeonContext, pgm: Program): Program = {
    // TODO: remove side-effects
    for (fd <- pgm.definedFunctions) {
      fd.fullBody = convertHoles(fd.fullBody,ctx)
    }

    pgm
  }

  def toExpr(h: Hole): (Expr, List[Identifier]) = {
    h.alts match {
      case Seq() =>
        val h1 = FreshIdentifier("hole", h.getType, true)
        (h1.toVariable, List(h1))

      case Seq(v) =>
        val h1 = FreshIdentifier("hole", BooleanType, true)
        val h2 = FreshIdentifier("hole", h.getType, true)
        (IfExpr(h1.toVariable, h2.toVariable, v), List(h1, h2))

      case exs =>
        var ids: List[Identifier] = Nil
        val ex = exs.init.foldRight(exs.last)({ (e: Expr, r: Expr) =>
          val h = FreshIdentifier("hole", BooleanType, true)
          ids ::= h
          IfExpr(h.toVariable, e, r)
        })

        (ex, ids.reverse)
    }
  }
}
