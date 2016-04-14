/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import Common._
import Definitions._
import Expressions._
import xlang.Expressions._
import Extractors._
import Types._

import utils._
import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

trait TreeTransformer {
  def transform(id: Identifier): Identifier = id
  def transform(cd: ClassDef): ClassDef = cd
  def transform(fd: FunDef): FunDef = fd

  def transform(e: Expr)(implicit bindings: Map[Identifier, Identifier]): Expr = e match {
    case Variable(id) if bindings contains id => Variable(bindings(id)).copiedFrom(e)
    case Variable(id) => Variable(transform(id)).copiedFrom(e)
    case FiniteLambda(mappings, default, tpe) =>
      FiniteLambda(mappings.map { case (ks, v) => (ks map transform, transform(v)) },
        transform(default), transform(tpe).asInstanceOf[FunctionType]).copiedFrom(e)
    case Lambda(args, body) =>
      val newArgs = args.map(vd => ValDef(transform(vd.id)))
      val newBindings = (args zip newArgs).map(p => p._1.id -> p._2.id)
      Lambda(newArgs, transform(body)(bindings ++ newBindings)).copiedFrom(e)
    case Forall(args, body) =>
      val newArgs = args.map(vd => ValDef(transform(vd.id)))
      val newBindings = (args zip newArgs).map(p => p._1.id -> p._2.id)
      Forall(newArgs, transform(body)(bindings ++ newBindings)).copiedFrom(e)
    case Let(a, expr, body) =>
      val newA = transform(a)
      Let(newA, transform(expr), transform(body)(bindings + (a -> newA))).copiedFrom(e)
    case LetVar(a, expr, body) =>
      val newA = transform(a)
      LetVar(newA, transform(expr), transform(body)(bindings + (a -> newA))).copiedFrom(e)
    case LetDef(fds, body) =>
      val rFds = fds map transform
      val rBody = transform(body)
      LetDef(rFds, rBody).copiedFrom(e)
    case CaseClass(cct, args) =>
      CaseClass(transform(cct).asInstanceOf[CaseClassType], args map transform).copiedFrom(e)
    case CaseClassSelector(cct, caseClass, selector) =>
      val newCct @ CaseClassType(ccd, _) = transform(cct)
      val newSelector = ccd.fieldsIds(cct.classDef.fieldsIds.indexOf(selector))
      CaseClassSelector(newCct, transform(caseClass), newSelector).copiedFrom(e)
    case FunctionInvocation(TypedFunDef(fd, tpes), args) =>
      FunctionInvocation(TypedFunDef(transform(fd), tpes map transform), args map transform).copiedFrom(e)
    case MethodInvocation(rec, cd, TypedFunDef(fd, tpes), args) =>
      MethodInvocation(transform(rec), transform(cd), TypedFunDef(transform(fd), tpes map transform), args map transform).copiedFrom(e)
    case This(ct) =>
      This(transform(ct).asInstanceOf[ClassType]).copiedFrom(e)
    case IsInstanceOf(expr, ct) =>
      IsInstanceOf(transform(expr), transform(ct).asInstanceOf[ClassType]).copiedFrom(e)
    case AsInstanceOf(expr, ct) => 
      AsInstanceOf(transform(expr), transform(ct).asInstanceOf[ClassType]).copiedFrom(e)
    case MatchExpr(scrutinee, cases) =>
      MatchExpr(transform(scrutinee), for (cse @ MatchCase(pattern, guard, rhs) <- cases) yield {
        val (newPattern, newBindings) = transform(pattern)
        val allBindings = bindings ++ newBindings
        MatchCase(newPattern, guard.map(g => transform(g)(allBindings)), transform(rhs)(allBindings)).copiedFrom(cse)
      }).copiedFrom(e)
    case Passes(in, out, cases) =>
      Passes(transform(in), transform(out), for (cse @ MatchCase(pattern, guard, rhs) <- cases) yield {
        val (newPattern, newBindings) = transform(pattern)
        val allBindings = bindings ++ newBindings
        MatchCase(newPattern, guard.map(g => transform(g)(allBindings)), transform(rhs)(allBindings)).copiedFrom(cse)
      }).copiedFrom(e)
    case FiniteSet(es, tpe) =>
      FiniteSet(es map transform, transform(tpe)).copiedFrom(e)
    case FiniteBag(es, tpe) =>
      FiniteBag(es map { case (k, v) => transform(k) -> v }, transform(tpe)).copiedFrom(e)
    case FiniteMap(pairs, from, to) =>
      FiniteMap(pairs map { case (k, v) => transform(k) -> transform(v) }, transform(from), transform(to)).copiedFrom(e)
    case EmptyArray(tpe) =>
      EmptyArray(transform(tpe)).copiedFrom(e)
    case Hole(tpe, alts) =>
      Hole(transform(tpe), alts map transform).copiedFrom(e)
    case NoTree(tpe) =>
      NoTree(transform(tpe)).copiedFrom(e)
    case Error(tpe, desc) =>
      Error(transform(tpe), desc).copiedFrom(e)
    case Operator(es, builder) =>
      val newEs = es map transform
      if ((newEs zip es).exists { case (bef, aft) => aft ne bef }) {
        builder(newEs).copiedFrom(e)
      } else {
        e
      }
    case e => e
  }

  def transform(pat: Pattern): (Pattern, Map[Identifier, Identifier]) = pat match {
    case InstanceOfPattern(binder, ct) =>
      val newBinder = binder map transform
      val newPat = InstanceOfPattern(newBinder, transform(ct).asInstanceOf[ClassType]).copiedFrom(pat)
      (newPat, (binder zip newBinder).toMap)
    case WildcardPattern(binder) =>
      val newBinder = binder map transform
      val newPat = WildcardPattern(newBinder).copiedFrom(pat)
      (newPat, (binder zip newBinder).toMap)
    case CaseClassPattern(binder, ct, subs) =>
      val newBinder = binder map transform
      val (newSubs, subBinders) = (subs map transform).unzip
      val newPat = CaseClassPattern(newBinder, transform(ct).asInstanceOf[CaseClassType], newSubs).copiedFrom(pat)
      (newPat, (binder zip newBinder).toMap ++ subBinders.flatten)
    case TuplePattern(binder, subs) =>
      val newBinder = binder map transform
      val (newSubs, subBinders) = (subs map transform).unzip
      val newPat = TuplePattern(newBinder, newSubs).copiedFrom(pat)
      (newPat, (binder zip newBinder).toMap ++ subBinders.flatten)
    case UnapplyPattern(binder, TypedFunDef(fd, tpes), subs) =>
      val newBinder = binder map transform
      val (newSubs, subBinders) = (subs map transform).unzip
      val newPat = UnapplyPattern(newBinder, TypedFunDef(transform(fd), tpes map transform), newSubs).copiedFrom(pat)
      (newPat, (binder zip newBinder).toMap ++ subBinders.flatten)
    case PatternExtractor(subs, builder) =>
      val (newSubs, subBinders) = (subs map transform).unzip
      (builder(newSubs).copiedFrom(pat), subBinders.flatten.toMap)
  }

  def transform(tpe: TypeTree): TypeTree = tpe match {
    case cct @ CaseClassType(ccd, args) =>
      CaseClassType(transform(ccd).asInstanceOf[CaseClassDef], args map transform).copiedFrom(tpe)
    case act @ AbstractClassType(acd, args) =>
      AbstractClassType(transform(acd).asInstanceOf[AbstractClassDef], args map transform).copiedFrom(tpe)
    case NAryType(ts, builder) => builder(ts map transform).copiedFrom(tpe)
  }
}

trait TreeTraverser {
  def traverse(id: Identifier): Unit = ()
  def traverse(cd: ClassDef): Unit = ()
  def traverse(fd: FunDef): Unit = ()

  def traverse(e: Expr): Unit = e match {
    case Variable(id) => traverse(id)
    case FiniteLambda(mappings, default, tpe) =>
      (default +: mappings.toSeq.flatMap(p => p._2 +: p._1)) foreach traverse
      traverse(tpe)
    case Lambda(args, body) =>
      args foreach (vd => traverse(vd.id))
      traverse(body)
    case Forall(args, body) =>
      args foreach (vd => traverse(vd.id))
      traverse(body)
    case Let(a, expr, body) =>
      traverse(a)
      traverse(expr)
      traverse(body)
    case CaseClass(cct, args) =>
      traverse(cct)
      args foreach traverse
    case CaseClassSelector(cct, caseClass, selector) =>
      traverse(cct)
      traverse(caseClass)
    case FunctionInvocation(TypedFunDef(fd, tpes), args) =>
      traverse(fd)
      tpes foreach traverse
      args foreach traverse
    case MethodInvocation(rec, cd, TypedFunDef(fd, tpes), args) =>
      traverse(rec)
      traverse(cd)
      traverse(fd)
      tpes foreach traverse
      args foreach traverse
    case This(ct) =>
      traverse(ct)
    case IsInstanceOf(expr, ct) =>
      traverse(expr)
      traverse(ct)
    case AsInstanceOf(expr, ct) => 
      traverse(expr)
      traverse(ct)
    case MatchExpr(scrutinee, cases) =>
      traverse(scrutinee)
      for (cse @ MatchCase(pattern, guard, rhs) <- cases) {
        traverse(pattern)
        guard foreach traverse
        traverse(rhs)
      }
    case FiniteSet(es, tpe) =>
      es foreach traverse
      traverse(tpe)
    case FiniteBag(es, tpe) =>
      es foreach { case (k, _) => traverse(k) }
      traverse(tpe)
    case FiniteMap(pairs, from, to) =>
      pairs foreach { case (k, v) => traverse(k); traverse(v) }
      traverse(from)
      traverse(to)
    case EmptyArray(tpe) =>
      traverse(tpe)
    case Hole(tpe, alts) =>
      traverse(tpe)
      alts foreach traverse
    case NoTree(tpe) =>
      traverse(tpe)
    case Error(tpe, desc) =>
      traverse(tpe)
    case Operator(es, builder) =>
      es foreach traverse
    case e =>
  }

  def traverse(pat: Pattern): Unit = pat match {
    case InstanceOfPattern(binder, ct) =>
      binder foreach traverse
      traverse(ct)
    case WildcardPattern(binder) =>
      binder foreach traverse
    case CaseClassPattern(binder, ct, subs) =>
      binder foreach traverse
      traverse(ct)
      subs foreach traverse
    case TuplePattern(binder, subs) =>
      binder foreach traverse
      subs foreach traverse
    case UnapplyPattern(binder, TypedFunDef(fd, tpes), subs) =>
      binder foreach traverse
      traverse(fd)
      tpes foreach traverse
      subs foreach traverse
    case PatternExtractor(subs, builder) =>
      subs foreach traverse
  }

  def traverse(tpe: TypeTree): Unit = tpe match {
    case cct @ CaseClassType(ccd, args) =>
      traverse(ccd)
      args foreach traverse
    case act @ AbstractClassType(acd, args) =>
      traverse(acd)
      args foreach traverse
    case NAryType(ts, builder) =>
      ts foreach traverse
  }
}
