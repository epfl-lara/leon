/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

import purescala.Common._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Definitions._

object ConvertHoles extends LeonPhase[Program, Program] {
  val name        = "Convert Holes to Choose"
  val description = "Convert holes found in bodies to equivalent Choose"

  /**
   * This phase converts a body with "holes" into a choose construct:
   *
   * def foo(a: T) {
   *   require(..a..)
   *   expr(???, ???)
   * } ensuring { res => 
   *   pred(res)
   * }
   *
   * gets converted into:
   *
   * def foo(a: T) {
   *   require(..a..)
   *   choose { (c1, c2) => {
   *     val res = expr(c1, c2)
   *     pred(res)
   *   }
   * } ensuring { res => 
   *   pred(res)
   * }
   *
   */
  def run(ctx: LeonContext)(pgm: Program): Program = {
    pgm.definedFunctions.foreach(fd => {
      if (fd.hasPostcondition && fd.hasBody) {
        var holes = List[Identifier]()
        val body = preMap {
          case h @ Hole() =>
            val id = FreshIdentifier("c", true).copiedFrom(h)
            holes ::= id

            Some(id.toVariable)
          case _ => None
        }(fd.body.get)

        holes = holes.reverse

        if (holes.nonEmpty) {
          val res = FreshIdentifier("b", true).copiedFrom(body)
          val (pid, pbody) = fd.postcondition.get

          val c = Choose(holes, Let(res, body, replaceFromIDs(Map(pid -> res.toVariable), pbody)))

          if (holes.size > 1) {
            val newHoles = holes.map(_.freshen)
            fd.body = Some(LetTuple(newHoles, c.setPos(body), replaceFromIDs((holes zip newHoles.map(_.toVariable)).toMap, body)).setPos(body))
          } else {
            fd.body = Some(preMap {
              case h @ Hole() => Some(c.setPos(h))
              case _ => None
            }(fd.body.get))
          }
        }
      } else {
        // No post-condition: we replace holes with local-chooses without
        // predicates
        fd.body = fd.body.map { preMap {
          case h @ Hole() =>
            val id = FreshIdentifier("c", true).copiedFrom(h)
            Some(Choose(List(id), BooleanLiteral(true)).copiedFrom(h))
          case _ => None
        } }
      }
      
      // Ensure that holes are not found in pre and/or post conditions
      fd.precondition.foreach {
        preTraversal{
          case Hole() =>
            ctx.reporter.error("Hole expressions are not supported in preconditions. (function "+fd.id.asString(ctx)+")")
          case _ =>
        }
      }

      fd.postcondition.foreach { case (id, post) =>
        preTraversal{
          case Hole() =>
            ctx.reporter.error("Hole expressions are not supported in postconditions. (function "+fd.id.asString(ctx)+")")
          case _ =>
        }(post)
      }

    })

    pgm
  }
}
