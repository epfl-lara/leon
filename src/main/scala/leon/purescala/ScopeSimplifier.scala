/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package purescala

import Common._
import Definitions._
import Trees._
import TypeTrees._
import TreeOps._
import Extractors._

class ScopeSimplifier extends Transformer {
  case class Scope(inScope: Set[Identifier] = Set(), oldToNew: Map[Identifier, Identifier] = Map(), funDefs: Map[FunDef, FunDef] = Map()) {

    def register(oldNew: (Identifier, Identifier)): Scope = {
      val (oldId, newId) = oldNew
      copy(inScope = inScope + newId, oldToNew = oldToNew + oldNew)
    }

    def registerFunDef(oldNew: (FunDef, FunDef)): Scope = {
      copy(funDefs = funDefs + oldNew)
    }
  }

  protected def genId(id: Identifier, scope: Scope): Identifier = {
    val existCount = scope.inScope.count(_.name == id.name)

    FreshIdentifier(id.name, existCount).setType(id.getType)
  }

  protected def rec(e: Expr, scope: Scope): Expr = e match {
    case Let(i, e, b) =>
      val si = genId(i, scope)
      val se = rec(e, scope)
      val sb = rec(b, scope.register(i -> si))
      Let(si, se, sb)

    case LetDef(fd: FunDef, body: Expr) =>
      val newId    = genId(fd.id, scope)
      var newScope = scope.register(fd.id -> newId)

      val newArgs = for(VarDecl(id, tpe) <- fd.args) yield {
        val newArg = genId(id, newScope)
        newScope = newScope.register(id -> newArg)
        VarDecl(newArg, tpe)
      }

      val newFd = new FunDef(newId, fd.returnType, newArgs)

      newScope = newScope.registerFunDef(fd -> newFd)

      newFd.body          = fd.body.map(b => rec(b, newScope))
      newFd.precondition  = fd.precondition.map(pre => rec(pre, newScope))

      newFd.postcondition = fd.postcondition.map {
        case (id, post) =>
          val nid = genId(id, newScope)
          val postScope = newScope.register(id -> nid)
          (nid, rec(post, postScope))
      }

      LetDef(newFd, rec(body, newScope))

    case LetTuple(is, e, b) =>
      var newScope = scope
      val sis = for (i <- is) yield {
        val si = genId(i, newScope)
        newScope = newScope.register(i -> si)
        si
      }

      val se = rec(e, scope)
      val sb = rec(b, newScope)
      LetTuple(sis, se, sb)

    case MatchExpr(scrut, cases) =>
      val rs = rec(scrut, scope)

      def trPattern(p: Pattern, scope: Scope): (Pattern, Scope) = {
        val (newBinder, newScope) = p.binder match {
          case Some(id) =>
            val newId = genId(id, scope)
            val newScope = scope.register(id -> newId)
            (Some(newId), newScope)
          case None =>
            (None, scope)
        }

        var curScope = newScope
        var newSubPatterns = for (sp <- p.subPatterns) yield {
          val (subPattern, subScope) = trPattern(sp, curScope)
          curScope = subScope
          subPattern
        }

        val newPattern = p match {
          case InstanceOfPattern(b, ctd) =>
            InstanceOfPattern(newBinder, ctd)
          case WildcardPattern(b) =>
            WildcardPattern(newBinder)
          case CaseClassPattern(b, ccd, sub) =>
            CaseClassPattern(newBinder, ccd, newSubPatterns)
          case TuplePattern(b, sub) =>
            TuplePattern(newBinder, newSubPatterns)
        }


        (newPattern, curScope)
      }

      MatchExpr(rs, cases.map { c =>
        val (newP, newScope) = trPattern(c.pattern, scope)

        c match {
          case SimpleCase(p, rhs) =>
            SimpleCase(newP, rec(rhs, newScope))
          case GuardedCase(p, g, rhs) =>
            GuardedCase(newP, rec(g, newScope), rec(rhs, newScope))
        }
      })

    case Variable(id) =>
      Variable(scope.oldToNew.getOrElse(id, id))

    case FunctionInvocation(fd, args) =>
      val newFd = scope.funDefs.getOrElse(fd, fd)
      val newArgs = args.map(rec(_, scope))

      FunctionInvocation(newFd, newArgs)

    case UnaryOperator(e, builder) =>
      builder(rec(e, scope))

    case BinaryOperator(e1, e2, builder) =>
      builder(rec(e1, scope), rec(e2, scope))

    case NAryOperator(es, builder) =>
      builder(es.map(rec(_, scope)))

    case t : Terminal => t

    case _ =>
      sys.error("Expression "+e+" ["+e.getClass+"] is not extractable")
  }

  def transform(e: Expr): Expr = {
    rec(e, Scope())
  }
}
