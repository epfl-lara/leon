/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import scala.collection.mutable.ListBuffer
import Common._
import Definitions._
import Expressions._
import Extractors._
import Constructors.letDef

class ScopeSimplifier extends Transformer {
  case class Scope(inScope: Set[Identifier] = Set(), oldToNew: Map[Identifier, Identifier] = Map(), funDefs: Map[FunDef, FunDef] = Map()) {
    
    def register(oldNew: (Identifier, Identifier)): Scope = {
      val newId = oldNew._2
      copy(inScope = inScope + newId, oldToNew = oldToNew + oldNew)
    }
    
    def register(oldNews: Seq[(Identifier, Identifier)]): Scope = {
      (this /: oldNews){ case (oldScope, oldNew) => oldScope.register(oldNew) }
    }

    def registerFunDef(oldNew: (FunDef, FunDef)): Scope = {
      copy(funDefs = funDefs + oldNew)
    }
  }

  protected def genId(id: Identifier, scope: Scope): Identifier = {
    val existCount = scope.inScope.count(_.name == id.name)

    FreshIdentifier(id.name, existCount, id.getType)
  }

  protected def rec(e: Expr, scope: Scope): Expr = e match {
    case Let(i, e, b) =>
      val si = genId(i, scope)
      val se = rec(e, scope)
      val sb = rec(b, scope.register(i -> si))
      Let(si, se, sb)

    case LetDef(fds, body: Expr) =>
      var newScope: Scope = scope
      // First register all functions
      val fds_newIds = for(fd <- fds) yield {
        val newId    = genId(fd.id, scope)
        newScope = newScope.register(fd.id -> newId)
        (fd, newId)
      }
      
      val fds_mapping = for((fd, newId) <- fds_newIds) yield {
        val localScopeToRegister = ListBuffer[(Identifier, Identifier)]() // We record the mapping of these variables only for the function.
        val newArgs = for(ValDef(id) <- fd.params) yield {
          val newArg = genId(id, newScope.register(localScopeToRegister))
          localScopeToRegister += (id -> newArg) // This renaming happens only inside the function.
          ValDef(newArg)
        }
  
        val newFd = fd.duplicate(id = newId, params = newArgs)
  
        newScope = newScope.registerFunDef(fd -> newFd)
        (newFd, localScopeToRegister, fd)
      }
      
      for((newFd, localScopeToRegister, fd) <- fds_mapping) {
        newFd.fullBody = rec(fd.fullBody, newScope.register(localScopeToRegister))
      }
      letDef(fds_mapping.map(_._1), rec(body, newScope))
   
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
        val newSubPatterns = for (sp <- p.subPatterns) yield {
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
          case UnapplyPattern(b, obj, sub) =>
            UnapplyPattern(newBinder, obj, newSubPatterns)
          case LiteralPattern(_, lit) => 
            LiteralPattern(newBinder, lit)
        }

        (newPattern, curScope)
      }

      MatchExpr(rs, cases.map { c =>
        val (newP, newScope) = trPattern(c.pattern, scope)
        MatchCase(newP, c.optGuard map {rec(_, newScope)}, rec(c.rhs, newScope))
      })

    case Variable(id) =>
      Variable(scope.oldToNew.getOrElse(id, id))

    case FunctionInvocation(tfd, args) =>
      val newFd = scope.funDefs.getOrElse(tfd.fd, tfd.fd)
      val newArgs = args.map(rec(_, scope))

      FunctionInvocation(newFd.typed(tfd.tps), newArgs)

    case Operator(es, builder) =>
      builder(es.map(rec(_, scope)))

    case _ =>
      sys.error("Expression "+e+" ["+e.getClass+"] is not extractable")
  }

  def transform(e: Expr): Expr = {
    rec(e, Scope())
  }
}
