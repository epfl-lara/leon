/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import Common._
import Definitions._
import Expressions._
import Constructors._
import ExprOps._
import Types._

object Path {
  final type Element = Either[(Identifier, Expr), Expr]
  def empty: Path = new Path(Seq.empty)
  def apply(p: Expr): Path = p match {
    case Let(i, e, b) => new Path(Seq(Left(i -> e))) merge apply(b)
    case _ => new Path(Seq(Right(p)))
  }
  def apply(path: Seq[Expr]): Path = new Path(path.map(Right(_)))
}

/** Encodes path conditions
  * 
  * Paths are encoded as an (ordered) series of let-bindings and boolean
  * propositions. A path is satisfiable iff all propositions are true
  * in the context of the provided let-bindings.
  *
  * This encoding enables let-bindings over types for which equality is
  * not defined, whereas an encoding of let-bindings with equalities
  * could introduce non-sensical equations.
  */
class Path private[purescala](
  private[purescala] val elements: Seq[Path.Element]) extends Printable {

  import Path.Element
  
  /** Add a binding to this [[Path]] */
  def withBinding(p: (Identifier, Expr)) = {
    def exprOf(e: Element) = e match { case Right(e) => e; case Left((_, e)) => e }
    val (before, after) = elements span (el => !variablesOf(exprOf(el)).contains(p._1))
    new Path(before ++ Seq(Left(p)) ++ after)
  }
  def withBindings(ps: Iterable[(Identifier, Expr)]) = {
    ps.foldLeft(this)( _ withBinding _ )
  }

  /** Add a condition to this [[Path]] */
  def withCond(e: Expr) = {
    if (e == BooleanLiteral(true)) this
    else new Path(elements :+ Right(e))
  }
  def withConds(es: Iterable[Expr]) = new Path(elements ++ es.filterNot( _ == BooleanLiteral(true)).map(Right(_)))

  /** Remove bound variables from this [[Path]]
    * @param ids the bound variables to remove
    */
  def --(ids: Set[Identifier]) = new Path(elements.filterNot(_.left.exists(p => ids(p._1))))

  /** Appends `that` path at the end of `this` */
  def merge(that: Path) = new Path(elements ++ that.elements)

  /** Transforms all expressions inside the path
    *
    * Expressions in a path appear both on the right-hand side of let binders
    * and in boolean path conditions.
    */
  def map(f: Expr => Expr) = new Path(elements.map(_.left.map { case (id, e) => id -> f(e) }.right.map(f)))

  /** Splits the path on predicate `p`
    *
    * The path is split into
    * 1. the sub-path containing all conditions that pass `p` (and all let-bindings), and
    * 2. the sequence of conditions that didn't pass `p`.
    */
  def partition(p: Expr => Boolean): (Path, Seq[Expr]) = {
    val (passed, failed) = elements.partition {
      case Right(e) => p(e)
      case Left(_) => true
    }

    (new Path(passed), failed.flatMap(_.right.toOption))
  }

  /** Check if the path is empty
    *
    * A path is empty iff it contains no let-bindings and its path condition is trivial.
    */
  def isEmpty = elements.forall {
    case Right(BooleanLiteral(true)) => true
    case _ => false
  }

  /** Returns the negation of a path
    *
    * Path negation requires folding the path into a proposition and negating it.
    * However, all external let-binders can be preserved in the resulting path, thus
    * avoiding let-binding dupplication in future path foldings.
    */
  def negate: Path = {
    val (outers, rest) = elements.span(_.isLeft)
    new Path(outers :+ Right(not(fold[Expr](BooleanLiteral(true), let, Constructors.and(_, _))(rest))))
  }

  /** Returns a new path which depends ONLY on provided ids.
    *
    * Let-bindings obviously depend on some `id` if it corresponds to the bound
    * identifier. An expression depends on an `id` iff the identifier is
    * contained within the expression.
    *
    * This method makes little sense on its own and will typically be used from
    * within a fixpoint computation where the `ids` set is iteratively computed
    * by performing [[filterByIds]] calls on some (unchaning) base [[Path]].
    *
    * @see [[leon.purescala.FunctionClosure.close]] for an example usecase.
    */
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

  /** Free variables within the path */
  lazy val variables: Set[Identifier] = fold[Set[Identifier]](Set.empty,
    (id, e, res) => res - id ++ variablesOf(e), (e, res) => res ++ variablesOf(e)
  )(elements)

  lazy val bindings: Seq[(Identifier, Expr)] = elements.collect { case Left(p) => p }
  lazy val boundIds = bindings map (_._1)
  lazy val conditions: Seq[Expr] = elements.collect { case Right(e) => e }

  def isBound(id: Identifier): Boolean = bindings.exists(p => p._1 == id)

  /** Fold the path elements
    *
    * This function takes two combiner functions, one for let bindings and one
    * for proposition expressions.
    */
  private def fold[T](base: T, combineLet: (Identifier, Expr, T) => T, combineCond: (Expr, T) => T)
                     (elems: Seq[Element]): T = elems.foldRight(base) {
    case (Left((id, e)), res) => combineLet(id, e, res)
    case (Right(e), res) => combineCond(e, res)
  }

  /** Folds the path elements over a distributive proposition combinator [[combine]]
    * 
    * Certain combiners can be distributive over let-binding folds. Namely, one
    * requires that `combine(let a = b in e1, e2)` be equivalent to
    * `let a = b in combine(e1, e2)` (where a \not\in FV(e2)). This is the case for
    * - conjunction [[and]]
    * - implication [[implies]]
    */
  private def distributiveClause(base: Expr, combine: (Expr, Expr) => Expr): Expr = {
    val (outers, rest) = elements.span(_.isLeft)
    val inner = fold[Expr](base, let, combine)(rest)
    fold[Expr](inner, let, (_,_) => scala.sys.error("Should never happen!"))(outers)
  }

  /** Folds the path into a conjunct with the expression `base` */
  def and(base: Expr) = distributiveClause(base, Constructors.and(_, _))

  /** Fold the path into an implication of `base`, namely `path ==> base` */
  def implies(base: Expr) = distributiveClause(base, Constructors.implies)

  /** Folds the path into a `require` wrapping the expression `body`
    *
    * The function takes additional optional parameters
    * - [[pre]] if one wishes to mix a pre-existing precondition into the final
    *   [[leon.purescala.Expressions.Require]], and
    * - [[post]] for mixing a postcondition ([[leon.purescala.Expressions.Ensuring]]) in.
    */
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

  /** Folds the path into the associated boolean proposition */
  lazy val toClause: Expr = and(BooleanLiteral(true))

  /** Like [[toClause]] but doesn't simplify final path through constructors
    * from [[leon.purescala.Constructors]] */
  lazy val fullClause: Expr = fold[Expr](BooleanLiteral(true), Let, And(_, _))(elements)

  /** Folds the path into a boolean proposition where let-bindings are
    * replaced by equations.
    *
    * CAUTION: Should only be used once INSIDE the solver!!
    */
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

