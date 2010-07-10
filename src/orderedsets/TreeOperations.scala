package orderedsets

import scala.collection.mutable.{Set => MutableSet}

import purescala._
import Trees._
import Common._
import TypeTrees._
import Definitions._

object TreeOperations {
  def dnf(expr: Expr): Stream[Seq[Expr]] = expr match {
    case And(Nil) => Stream(Nil)
    case And(c :: Nil) => dnf(c)
    case And(c :: cs) =>
      for (conj1 <- dnf(c); conj2 <- dnf(And(cs)))
      yield conj1 ++ conj2
    case Or(Nil) => Stream(Seq(BooleanLiteral(false)))
    case Or(d :: Nil) => dnf(d)
    case Or(d :: ds) => dnf(d) append dnf(Or(ds))
    // Rewrite Iff and Implies
    case Iff(p, q) =>
      dnf(Or(And(p, q), And(negate(p), negate(q))))
    case Implies(p, q) =>
      dnf(Or(negate(p), q))
    // Convert to nnf
    case Not(e@(And(_) | Or(_) | Iff(_, _) | Implies(_, _))) =>
      dnf(negate(e))
    case _ => Stream(expr :: Nil)
  }

  def searchAndReplace(subst: Expr => Option[Expr], recursive: Boolean = true)(expr: Expr) = {
    def rec(ex: Expr, skip: Expr = null): Expr = (if (ex == skip) None else subst(ex)) match {
      case Some(newExpr) => {
        if (newExpr.getType == NoType) {
          Settings.reporter.warning("REPLACING IN EXPRESSION WITH AN UNTYPED TREE ! " + ex + " --to--> " + newExpr)
        }
        if (ex == newExpr)
          if (recursive) rec(ex, ex) else ex
        else
        if (recursive) rec(newExpr) else newExpr
      }
      case None => ex match {
        case l@Let(i, e, b) => {
          val re = rec(e)
          val rb = rec(b)
          if (re != e || rb != b)
            Let(i, re, rb).setType(l.getType)
          else
            l
        }
        case f@FunctionInvocation(fd, args) => {
          var change = false
          val rargs = args.map(a => {
            val ra = rec(a)
            if (ra != a) {
              change = true
              ra
            } else {
              a
            }
          })
          if (change)
            FunctionInvocation(fd, rargs).setType(f.getType)
          else
            f
        }
        case i@IfExpr(t1, t2, t3) => IfExpr(rec(t1), rec(t2), rec(t3)).setType(i.getType)
        case m@MatchExpr(scrut, cses) => MatchExpr(rec(scrut), cses.map(inCase(_))).setType(m.getType)
        case And(exs) => And(exs.map(rec(_)))
        case Or(exs) => Or(exs.map(rec(_)))
        case Not(e) => Not(rec(e))
        case u@UnaryOperator(t, recons) => {
          val r = rec(t)
          if (r != t)
            recons(r).setType(u.getType)
          else
            u
        }
        case b@BinaryOperator(t1, t2, recons) => {
          val r1 = rec(t1)
          val r2 = rec(t2)
          if (r1 != t1 || r2 != t2)
            recons(r1, r2).setType(b.getType)
          else
            b
        }
        case c@CaseClass(cd, args) => {
          CaseClass(cd, args.map(rec(_))).setType(c.getType)
        }
        case c@CaseClassSelector(cc, sel) => {
          val rc = rec(cc)
          if (rc != cc)
            CaseClassSelector(rc, sel).setType(c.getType)
          else
            c
        }

        case f @ FiniteSet(elems) => {
          FiniteSet(elems.map(rec(_))).setType(f.getType)
        }

        case _ => ex
      }
    }

    def inCase(cse: MatchCase): MatchCase = cse match {
      case SimpleCase(pat, rhs) => SimpleCase(pat, rec(rhs))
      case GuardedCase(pat, guard, rhs) => GuardedCase(pat, rec(guard), rec(rhs))
    }

    rec(expr)
  }

  def asCatamorphism(program: Program, f: FunDef): Option[Seq[(CaseClassDef, Identifier, Seq[Identifier], Expr)]] = {
    def recCallsOnMatchedVars(l: (CaseClassDef, Identifier, Seq[Identifier], Expr)) = {
      var varSet = MutableSet.empty[Identifier]
      searchAndReplace({case FunctionInvocation(_, Seq(Variable(id))) => varSet += id; None; case _ => None})(l._4)
      varSet.subsetOf(l._3.toSet)
    }

    val c = program.callees(f)
    if (f.hasImplementation && f.args.size == 1 && c.size == 1 && c.head == f) f.body.get match {
      case SimplePatternMatching(scrut, _, lstMatches)
        if (scrut == f.args.head.toVariable) && lstMatches.forall(recCallsOnMatchedVars) => Some(lstMatches)
      case _ => None
    } else {
      None
    }
  }
}
