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
        case f@FiniteSet(elems) => {
          FiniteSet(elems.map(rec(_))).setType(f.getType)
        }
        case Terminal() => ex   // Ok
        case _ => error("Unsupported case in searchAndReplace : " + ex.getClass) // Missed case
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
  
  // 'Lazy' rewriter
  // 
  // Hoists if expressions to the top level and
  // transforms them to disjunctions.
  //
  // The implementation is totally brain-teasing
  def rewrite(expr: Expr): Expr =
    rewrite(expr, ex => ex)
  
  private def rewrite(expr: Expr, context: Expr => Expr): Expr = expr match {
    case IfExpr(_c, _t, _e) =>
      rewrite(_c, c =>
        rewrite(_t, t =>
          rewrite(_e, e =>
            Or(And(c, context(t)), And(negate(c), context(e)))
          )))
    case And(_exs) =>
      rewrite_*(_exs, exs =>
        context(And(exs)))
    case Or(_exs) =>
      rewrite_*(_exs, exs =>
        context(Or(exs)))
    case Not(_ex) =>
      rewrite(_ex, ex => 
        context(Not(ex)))
    case f@FunctionInvocation(fd, _args) =>
      rewrite_*(_args, args =>
        context(FunctionInvocation(fd, args) setType f.getType))
    case u@UnaryOperator(_t, recons) =>
      rewrite(_t, t =>
        context(recons(t) setType u.getType))
    case b@BinaryOperator(_t1, _t2, recons) =>
      rewrite(_t1, t1 => 
        rewrite(_t2, t2 => 
          context(recons(t1, t2) setType b.getType)))
    case c@CaseClass(cd, _args) =>
      rewrite_*(_args, args =>
        context(CaseClass(cd, args) setType c.getType))
    case c@CaseClassSelector(_cc, sel) =>
      rewrite(_cc, cc =>
        context(CaseClassSelector(cc, sel) setType c.getType))
    case f@FiniteSet(_elems) =>
      rewrite_*(_elems, elems =>
        context(FiniteSet(elems) setType f.getType))
    case Terminal() =>
      context(expr)
    case _ => // Missed case
      error("Unsupported case in rewrite : " + expr.getClass)
  }
  
  private def rewrite_*(exprs: Seq[Expr], context: Seq[Expr] => Expr): Expr =
    exprs match {
      case Nil => context(Nil)
      case _t :: _ts =>
        rewrite(_t, t => rewrite_*(_ts, ts => context(t +: ts)))
    }
  
  // This should rather be a marker interface, but I don't want
  // to change Trees.scala without Philippe's permission.
  object Terminal {
    def unapply(expr: Expr): Boolean = expr match {
      case Variable(_) | ResultVariable() | OptionNone(_) | EmptySet(_) | EmptyMultiset(_) | EmptyMap(_, _) | NilList(_) => true
      case _: Literal[_] => true
      case _ => false
    }
  }
  
  
  
}
