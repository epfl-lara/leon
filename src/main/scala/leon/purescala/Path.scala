/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import Common._
import Definitions._
import Expressions._
import Constructors._
import Extractors._
import ExprOps._
import Types._

object Path {
  def empty: Path = new Path(Seq.empty)
  def apply(p: Expr): Path = p match {
    case Let(i, e, b) => new Path(Seq(Left(i -> e))) merge apply(b)
    case _ => new Path(Seq(Right(p)))
  }
  def apply(path: Seq[Expr]): Path = new Path(path.map(Right(_)))
}

/** Encodes path conditions */
class Path private[purescala](
  private[purescala] val elements: Seq[Either[(Identifier, Expr), Expr]]) {

  def withBinding(p: (Identifier, Expr)) = new Path(elements :+ Left(p))
  def withBindings(ps: Iterable[(Identifier, Expr)]) = new Path(elements ++ ps.map(Left(_)))
  def withCond(e: Expr) = new Path(elements :+ Right(e))
  def withConds(es: Iterable[Expr]) = new Path(elements ++ es.map(Right(_)))

  def --(ids: Set[Identifier]) = new Path(elements.filterNot(_.left.exists(p => ids(p._1))))

  def merge(that: Path) = new Path(elements ++ that.elements)

  def map(f: Expr => Expr) = new Path(elements.map(_.left.map { case (id, e) => id -> f(e) }.right.map(f)))
  def partition(p: Expr => Boolean): (Path, Seq[Expr]) = {
    val (passed, failed) = elements.partition {
      case Right(e) => p(e)
      case Left(_) => true
    }

    (new Path(passed), failed.flatMap(_.right.toOption))
  }

  def isEmpty = elements.filter {
    case Right(BooleanLiteral(true)) => false
    case _ => true
  }.isEmpty

  def negate: Path = {
    val (outers, rest) = elements.span(_.isLeft)
    new Path(outers :+ Right(not(fold[Expr](BooleanLiteral(true), let, Constructors.and(_, _))(rest))))
  }

  def filterByIds(ids: Set[Identifier]): Path = {
    def containsIds(ids: Set[Identifier])(e: Expr): Boolean = exists{
      case Variable(id) => ids.contains(id)
      case _ => false
    }(e)
    
    val newElements = elements.filter{
      case Left((id, e)) => ids.contains(id) || containsIds(ids)(e)
      case Right(e) => containsIds(ids)(e)
    }
    new Path(newElements)
  }

  lazy val variables: Set[Identifier] = fold[Set[Identifier]](Set.empty,
    (id, e, res) => res - id ++ variablesOf(e), (e, res) => res ++ variablesOf(e)
  )(elements)

  lazy val bindings: Seq[(Identifier, Expr)] = elements.collect { case Left(p) => p }
  lazy val conditions: Seq[Expr] = elements.collect { case Right(e) => e }

  private def fold[T](base: T, combineLet: (Identifier, Expr, T) => T, combineCond: (Expr, T) => T)
                     (elems: Seq[Either[(Identifier, Expr), Expr]]): T = elems.foldRight(base) {
    case (Left((id, e)), res) => combineLet(id, e, res)
    case (Right(e), res) => combineCond(e, res)
  }

  private def distributiveClause(base: Expr, combine: (Expr, Expr) => Expr): Expr = {
    val (outers, rest) = elements.span(_.isLeft)
    val inner = fold[Expr](base, let, combine)(rest)
    fold[Expr](inner, let, (_,_) => scala.sys.error("Should never happen!"))(outers)
  }

  def and(base: Expr) = distributiveClause(base, Constructors.and(_, _))
  def implies(base: Expr) = distributiveClause(base, Constructors.implies(_, _))
  def specs(body: Expr, pre: Expr = BooleanLiteral(true), post: Expr = NoTree(BooleanType)) = {
    val (outers, rest) = elements.span(_.isLeft)
    val cond = fold[Expr](BooleanLiteral(true), let, Constructors.and(_, _))(rest)

    def wrap(e: Expr): Expr = {
      val bindings = rest.collect { case Left((id, e)) => id -> e }
      val idSubst = bindings.map(p => p._1 -> p._1.freshen).toMap
      val substMap = idSubst.mapValues(_.toVariable)
      val replace = replaceFromIDs(substMap, _: Expr)
      bindings.foldRight(replace(e)) { case ((id, e), b) => let(idSubst(id), replace(e), b) }
    }

    val req = Require(Constructors.and(cond, wrap(pre)), wrap(body))
    val full = post match {
      case l @ Lambda(args, body) => Ensuring(req, Lambda(args, wrap(body)).copiedFrom(l))
      case _ => req
    }

    fold[Expr](full, let, (_, _) => scala.sys.error("Should never happen!"))(outers)
  }

  lazy val toClause: Expr = and(BooleanLiteral(true))
  lazy val fullClause: Expr = fold[Expr](BooleanLiteral(true), Let(_, _, _), And(_, _))(elements)

  lazy val toPath: Expr = andJoin(elements.map {
    case Left((id, e)) => Equals(id.toVariable, e)
    case Right(e) => e
  })

  override def equals(that: Any): Boolean = that match {
    case p: Path => elements == p.elements
    case _ => false
  }

  override def hashCode: Int = elements.hashCode

  override def toString = asString(LeonContext.printNames)
  def asString(implicit ctx: LeonContext): String = fullClause.asString
  def asString(pgm: Program)(implicit ctx: LeonContext): String = fullClause.asString(pgm)
}

