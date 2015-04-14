/* Copyright 2009-2015 EPFL, Lausanne */

package leon.xlang

import leon.UnitPhase
import leon.LeonContext
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.xlang.Expressions._
import leon.purescala.Extractors._
import leon.purescala.Types._

object ArrayTransformation extends UnitPhase[Program] {

  val name = "Array Transformation"
  val description = "Add bound checking for array access and remove array update with side effect"

  def apply(ctx: LeonContext, pgm: Program) = {
    pgm.definedFunctions.foreach(fd => {
      fd.fullBody = transform(fd.fullBody)(Map())
    })
  }

  def transform(expr: Expr)(implicit env: Map[Identifier, Identifier]): Expr = (expr match {
    case up@ArrayUpdate(a, i, v) => {
      val ra = transform(a)
      val ri = transform(i)
      val rv = transform(v)
      val Variable(id) = ra
      Assignment(id, ArrayUpdated(ra, ri, rv).setPos(up))
    }
    case Let(i, v, b) => {
      v.getType match {
        case ArrayType(_) => {
          val freshIdentifier = FreshIdentifier("t", i.getType)
          val newEnv = env + (i -> freshIdentifier)
          LetVar(freshIdentifier, transform(v)(newEnv), transform(b)(newEnv))
        }
        case _ => Let(i, transform(v), transform(b))
      }
    }
    case v@Variable(i) => {
      Variable(env.getOrElse(i, i))
    }

    case n @ NAryOperator(args, recons) => recons(args.map(transform))
    case b @ BinaryOperator(a1, a2, recons) => recons(transform(a1), transform(a2))
    case u @ UnaryOperator(a, recons) => recons(transform(a))

    case (t: Terminal) => t
    case unhandled => scala.sys.error("Non-terminal case should be handled in ArrayTransformation: " + unhandled)
  }).setPos(expr)

}
