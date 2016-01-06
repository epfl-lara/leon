/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis

import purescala.Common._
import purescala.Expressions._
import purescala.Types._
import purescala.ExprOps._
import purescala.Definitions._
import purescala.Constructors._

object ConversionPhase extends UnitPhase[Program] {
  val name        = "Eliminate holes, withOracle and abstract definitions"
  val description = "Convert Holes, withOracle found in bodies and abstract function bodies to equivalent Choose"

  /**
   * This phase does 3 things:
   *
   * 1) Converts a body with "withOracle{ .. }" into a choose construct:
   *
   * def foo(a: T) = {
   *   require(..a..)
   *   withOracle { o =>
   *     expr(a,o) ensuring { x => post(x) }
   *   }
   * }
   *
   * gets converted into:
   *
   * def foo(a: T) {
   *   require(..a..)
   *   val o = choose { (o) => {
   *     val res = expr(a, o)
   *     pred(res)
   *   }
   *   expr(a,o)
   * } ensuring { res =>
   *   pred(res)
   * }
   *
   *
   * 2) Converts a body with "???" into a choose construct:
   *
   * def foo(a: T) = {
   *   require(..a..)
   *   expr(a, ???)
   * } ensuring { x => post(x) }
   *
   * gets converted into:
   *
   * def foo(a: T) = {
   *   require(..a..)
   *   val h = choose ( h' =>
   *     val res = expr(a, h')
   *     post(res)
   *   )
   *   expr(a, h)
   * } ensuring { res =>
   *   post(res)
   * }
   *
   * 3) Completes abstract definitions:
   *
   *  def foo(a: T) = {
   *    require(..a..)
   *    _
   *  } ensuring { res =>
   *    post(res)
   *  }
   *
   *  gets converted to:
   *
   *  def foo(a: T) = {
   *    require(..a..)
   *    choose(x => post(x))
   *  }
   * (in practice, there will be no pre-and postcondition)
   *
   * 4) Functions that have only a choose as body gets their spec from the choose.
   *
   *  def foo(a: T) = {
   *    choose(x => post(a, x))
   *  }
   *
   *  gets converted to:
   *
   *  def foo(a: T) = {
   *    choose(x => post(a, x))
   *  } ensuring { x => post(a, x) }
   *
   * (in practice, there will be no pre-and postcondition)
   */

  def convert(e : Expr, ctx : LeonContext) : Expr = {
    val (pre, body, post) = breakDownSpecs(e)

    // Ensure that holes are not found in pre and/or post conditions
    (pre ++ post).foreach {
      preTraversal{
        case h : Hole =>
          ctx.reporter.error(s"Holes are not supported in pre- or postconditions. @ ${h.getPos}")
        case wo: WithOracle =>
          ctx.reporter.error(s"WithOracle expressions are not supported in pre- or postconditions: ${wo.asString(ctx)} @ ${wo.getPos}")
        case _ =>
      }
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

    val fullBody = body match {
      case Some(body) =>
        var holes  = List[Identifier]()

        val withoutHoles = preMap {
          case h : Hole =>
            val (expr, ids) = toExpr(h)

            holes ++= ids

            Some(expr)
          case wo @ WithOracle(os, b) =>
            withoutSpec(b) map { pred =>
              val chooseOs = os.map(_.freshen)

              val pred = post.getOrElse( // FIXME: We need to freshen variables
                Lambda(chooseOs.map(ValDef(_)), BooleanLiteral(true))
              )

              letTuple(os, Choose(pred), b)
            }
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

      case None =>
        val newPost = post getOrElse Lambda(Seq(ValDef(FreshIdentifier("res", e.getType))), BooleanLiteral(true))
        withPrecondition(Choose(newPost), pre)
    }

    // extract spec from chooses at the top-level
    fullBody match {
      case Require(_, Choose(spec)) =>
        withPostcondition(fullBody, Some(spec))
      case Choose(spec) =>
        withPostcondition(fullBody, Some(spec))
      case _ =>
        fullBody
    }
  }


  def apply(ctx: LeonContext, pgm: Program): Unit = {
    // TODO: remove side-effects
    for (fd <- pgm.definedFunctions) {
      fd.fullBody = convert(fd.fullBody,ctx)
    }
  }

}
