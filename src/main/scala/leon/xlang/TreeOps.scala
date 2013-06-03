/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package xlang

import purescala.Common._
import purescala.TypeTrees._
import purescala.Definitions._
import purescala.Trees._
import xlang.Trees._
import purescala.TreeOps._
import purescala.Extractors._

object TreeOps {

  //checking whether the expr is pure, that is do not contains any non-pure construct: assign, while, blocks, array, ...
  //this is expected to be true when entering the "backend" of Leon
  def isPure(expr: Expr): Boolean = {
    def convert(t: Expr) : Boolean = t match {
      case Block(_, _) => false
      case Assignment(_, _) => false
      case While(_, _) => false
      case LetVar(_, _, _) => false
      case LetDef(_, _) => false
      case ArrayUpdate(_, _, _) => false
      case ArrayMake(_) => false
      case ArrayClone(_) => false
      case Epsilon(_) => false
      case _ => true
    }
    def combine(b1: Boolean, b2: Boolean) = b1 && b2
    def compute(e: Expr, b: Boolean) = e match {
      case Block(_, _) => false
      case Assignment(_, _) => false
      case While(_, _) => false
      case LetVar(_, _, _) => false
      case LetDef(_, _) => false
      case ArrayUpdate(_, _, _) => false
      case ArrayMake(_) => false
      case ArrayClone(_) => false
      case Epsilon(_) => false
      case _ => b
    }
    treeCatamorphism(convert, combine, compute, expr)
  }

  def containsEpsilon(expr: Expr): Boolean = {
    def convert(t : Expr) : Boolean = t match {
      case (l : Epsilon) => true
      case _ => false
    }
    def combine(c1 : Boolean, c2 : Boolean) : Boolean = c1 || c2
    def compute(t : Expr, c : Boolean) = t match {
      case (l : Epsilon) => true
      case _ => c
    }
    treeCatamorphism(convert, combine, compute, expr)
  }

  def flattenBlocks(expr: Expr): Expr = {
    def applyToTree(expr: Expr): Option[Expr] = expr match {
      case Block(exprs, last) => {
        val nexprs = (exprs :+ last).flatMap{
          case Block(es2, el) => es2 :+ el
          case UnitLiteral => Seq()
          case e2 => Seq(e2)
        }
        val fexpr = nexprs match {
          case Seq() => UnitLiteral
          case Seq(e) => e
          case es => Block(es.init, es.last).setType(es.last.getType)
        }
        Some(fexpr)
      }
      case _ => None
    }
    searchAndReplaceDFS(applyToTree)(expr)
  }

  def containsLetDef(expr: Expr): Boolean = {
    def convert(t : Expr) : Boolean = t match {
      case (l : LetDef) => true
      case _ => false
    }
    def combine(c1 : Boolean, c2 : Boolean) : Boolean = c1 || c2
    def compute(t : Expr, c : Boolean) = t match {
      case (l : LetDef) => true
      case _ => c
    }
    treeCatamorphism(convert, combine, compute, expr)
  }

  trait ScopeSimplifier extends purescala.TreeOps.ScopeSimplifier {
    override def rec(e: Expr, scope: Scope) = e match { 
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
        newFd.postcondition = fd.postcondition.map(post => rec(post, newScope))


        LetDef(newFd, rec(body, newScope))

      case _ =>
        super.rec(e, scope)
    }
  }

}
