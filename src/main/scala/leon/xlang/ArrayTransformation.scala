/* Copyright 2009-2014 EPFL, Lausanne */

package leon.xlang

import leon.TransformationPhase
import leon.LeonContext
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.xlang.Trees._
import leon.purescala.Extractors._
import leon.purescala.Constructors._
import leon.purescala.TypeTrees._

object ArrayTransformation extends TransformationPhase {

  val name = "Array Transformation"
  val description = "Add bound checking for array access and remove array update with side effect"

  def apply(ctx: LeonContext, pgm: Program): Program = {
    pgm.definedFunctions.foreach(fd => {
      fd.fullBody = transform(fd.fullBody)(Map())
    })
    pgm
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

    case LetVar(id, e, b) => {
      val er = transform(e)
      val br = transform(b)
      LetVar(id, er, br)
    }
    case wh@While(c, e) => {
      val newWh = While(transform(c), transform(e))
      newWh.invariant = wh.invariant.map(i => transform(i))
      newWh.setPos(wh)
      newWh
    }

    case ite@IfExpr(c, t, e) => {
      val rc = transform(c)
      val rt = transform(t)
      val re = transform(e)
      IfExpr(rc, rt, re)
    }

    case m @ MatchExpr(scrut, cses) => {
      val scrutRec = transform(scrut)
      val csesRec = cses.map{ cse => MatchCase(cse.pattern, cse.optGuard map transform, transform(cse.rhs)) }
      val tpe = csesRec.head.rhs.getType
      matchExpr(scrutRec, csesRec).setPos(m)
    }
    case LetDef(fd, b) => {
      fd.fullBody = transform(fd.fullBody)
      val rb = transform(b)
      LetDef(fd, rb)
    }
    case n @ NAryOperator(args, recons) => recons(args.map(transform))
    case b @ BinaryOperator(a1, a2, recons) => recons(transform(a1), transform(a2))
    case u @ UnaryOperator(a, recons) => recons(transform(a))

    case (t: Terminal) => t
    case unhandled => scala.sys.error("Non-terminal case should be handled in ArrayTransformation: " + unhandled)
  }).setPos(expr)

}
