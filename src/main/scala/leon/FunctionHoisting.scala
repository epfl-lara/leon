package leon

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

object FunctionHoisting extends TransformationPhase {

  val name = "Function Hoisting"
  val description = "Hoist function at the top level"

  def apply(program: Program): Program = {
    val funDefs = program.definedFunctions
    var topLevelFuns: Set[FunDef] = Set()
    funDefs.foreach(fd => {
      val s2 = fd.body match {
        case Some(body) => {
          val (e2, s2) = hoist(body)
          fd.body = Some(e2)
          s2
        }
        case None => Set()
      }
      val s4 = fd.postcondition match {
        case Some(expr) => {
          val (e4, s4) = hoist(expr)
          fd.postcondition = Some(e4)
          s4
        }
        case None => Set()
      }
      topLevelFuns ++= (s2 ++ s4)
    })
    val Program(id, ObjectDef(objId, defs, invariants)) = program
    Program(id, ObjectDef(objId, defs ++ topLevelFuns, invariants))
  }

  private def hoist(expr: Expr): (Expr, Set[FunDef]) = expr match {
    case l @ LetDef(fd, rest) => {
      val (e, s) = hoist(rest)
      val s2 = fd.body match {
        case Some(body) => {
          val (e2, s2) = hoist(body)
          fd.body = Some(e2)
          s2
        }
        case None => Set()
      }
      val s4 = fd.postcondition match {
        case Some(expr) => {
          val (e4, s4) = hoist(expr)
          fd.postcondition = Some(e4)
          s4
        }
        case None => Set()
      }
      (e, (s ++ s2 ++ s4) + fd)
    }
    case l @ Let(i,e,b) => {
      val (re, s1) = hoist(e)
      val (rb, s2) = hoist(b)
      (Let(i, re, rb), s1 ++ s2)
    }
    case n @ NAryOperator(args, recons) => {
      val rargs = args.map(a => hoist(a))
      (recons(rargs.map(_._1)).setType(n.getType), rargs.flatMap(_._2).toSet)
    }
    case b @ BinaryOperator(t1,t2,recons) => {
      val (r1, s1) = hoist(t1)
      val (r2, s2) = hoist(t2)
      (recons(r1,r2).setType(b.getType), s1 ++ s2)
    }
    case u @ UnaryOperator(t,recons) => {
      val (r, s) = hoist(t)
      (recons(r).setType(u.getType), s)
    }
    case i @ IfExpr(t1,t2,t3) => {
      val (r1, s1) = hoist(t1)
      val (r2, s2) = hoist(t2)
      val (r3, s3) = hoist(t3)
      (IfExpr(r1, r2, r3).setType(i.getType), s1 ++ s2 ++ s3)
    }
    case m @ MatchExpr(scrut,cses) => {
      val (scrutRes, scrutSet) = hoist(scrut)
      val (csesRes, csesSets) = cses.map{
        case SimpleCase(pat, rhs) => {
          val (r, s) = hoist(rhs)
          (SimpleCase(pat, r), s)
        }
        case GuardedCase(pat, guard, rhs) => {
          val (r, s) = hoist(rhs)
          (GuardedCase(pat, guard, r), s)
        }
      }.unzip
      (MatchExpr(scrutRes, csesRes).setType(m.getType).setPosInfo(m), csesSets.toSet.flatten ++ scrutSet)
    }
    case t if t.isInstanceOf[Terminal] => (t, Set())
    case unhandled => scala.sys.error("Non-terminal case should be handled in FunctionHoisting: " + unhandled)
  }

}

// vim: set ts=4 sw=4 et:
