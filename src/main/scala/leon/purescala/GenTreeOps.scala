/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import Common._
import utils._

/** A type that pattern matches agains a type of [[Tree]] and extracts it subtrees,
  * and a builder that reconstructs a tree of the same type from subtrees.
  *
  * @tparam SubTree The type of the tree
  */
trait TreeExtractor[SubTree <: Tree] {
  def unapply(e: SubTree): Option[(Seq[SubTree], (Seq[SubTree]) => SubTree)]
}

/** Generic tree traversals based on a deconstructor of a specific tree type
  *
  * @tparam SubTree The type of the tree
  */
trait GenTreeOps[SubTree <: Tree]  {

  /** An extractor for [[SubTree]]*/
  val Deconstructor: TreeExtractor[SubTree]

  /* ========
   * Core API
   * ========
   *
   * All these functions should be stable, tested, and used everywhere. Modify
   * with care.
   */

  /** Does a right tree fold
    *
    * A right tree fold applies the input function to the subnodes first (from left
    * to right), and combine the results along with the current node value.
    *
    * @param f a function that takes the current node and the seq
    *        of results form the subtrees.
    * @param e The value on which to apply the fold.
    * @return The expression after applying `f` on all subtrees.
    * @note the computation is lazy, hence you should not rely on side-effects of `f`
    */
  def fold[T](f: (SubTree, Seq[T]) => T)(e: SubTree): T = {
    val rec = fold(f) _
    val Deconstructor(es, _) = e

    //Usages of views makes the computation lazy. (which is useful for
    //contains-like operations)
    f(e, es.view.map(rec))
  }
  
  
  /** Pre-traversal of the tree.
    *
    * Invokes the input function on every node '''before''' visiting
    * children. Traverse children from left to right subtrees.
    *
    * e.g.
    * {{{
    *   Add(a, Minus(b, c))
    * }}}
    * will yield, in order:
    * {{{
    *   f(Add(a, Minus(b, c))); f(a); f(Minus(b, c)); f(b); f(c)
    * }}}
    *
    * @param f a function to apply on each node of the expression
    * @param e the expression to traverse
    */
  def preTraversal(f: SubTree => Unit)(e: SubTree): Unit = {
    val rec = preTraversal(f) _
    val Deconstructor(es, _) = e
    f(e)
    es.foreach(rec)
  }

  /** Post-traversal of the tree.
    *
    * Invokes the input function on every node '''after''' visiting
    * children.
    *
    * e.g.
    * {{{
    *   Add(a, Minus(b, c))
    * }}}
    * will yield, in order:
    * {{{
    *   f(a), f(b), f(c), f(Minus(b, c)), f(Add(a, Minus(b, c)))
    * }}}
    *
    * @param f a function to apply on each node of the expression
    * @param e the expression to traverse
    */
  def postTraversal(f: SubTree => Unit)(e: SubTree): Unit = {
    val rec = postTraversal(f) _
    val Deconstructor(es, _) = e
    es.foreach(rec)
    f(e)
  }

  /** Pre-transformation of the tree.
    *
    * Takes a partial function of replacements and substitute
    * '''before''' recursing down the trees.
    *
    * Supports two modes :
    *
    *   - If applyRec is false (default), will only substitute once on each level.
    *
    *   e.g.
    *   {{{
    *     Add(a, Minus(b, c)) with replacements: Minus(b,c) -> d, b -> e, d -> f
    *   }}}
    *   will yield:
    *   {{{
    *     Add(a, d)   // And not Add(a, f) because it only substitute once for each level.
    *   }}}
    *
    *   - If applyRec is true, it will substitute multiple times on each level:
    *
    *   e.g.
    *   {{{
    *   Add(a, Minus(b, c)) with replacements: Minus(b,c) -> d, b -> e, d -> f
    *   }}}
    *   will yield:
    *   {{{
    *   Add(a, f)
    *   }}}
    *
    * @note The mode with applyRec true can diverge if f is not well formed
    */
  def preMap(f: SubTree => Option[SubTree], applyRec : Boolean = false)(e: SubTree): SubTree = {
    def g(t: SubTree, u: Unit): (Option[SubTree], Unit) = (f(t), ())
    preMapWithContext[Unit](g, applyRec)(e, ())
  }
  
  
  /** Post-transformation of the tree.
    *
    * Takes a partial function of replacements.
    * Substitutes '''after''' recursing down the trees.
    *
    * Supports two modes :
    *
    *   - If applyRec is false (default), will only substitute once on each level.
    *   e.g.
    *   {{{
    *     Add(a, Minus(b, c)) with replacements: Minus(b,c) -> z, Minus(e,c) -> d, b -> e
    *   }}}
    *   will yield:
    *   {{{
    *     Add(a, Minus(e, c))
    *   }}}
    *
    *   - If applyRec is true, it will substitute multiple times on each level:
    *   e.g.
    *   {{{
    *     Add(a, Minus(b, c)) with replacements: Minus(e,c) -> d, b -> e, d -> f
    *   }}}
    *   will yield:
    *   {{{
    *     Add(a, f)
    *   }}}
    *
    * @note The mode with applyRec true can diverge if f is not well formed (i.e. not convergent)
    */
  def postMap(f: SubTree => Option[SubTree], applyRec : Boolean = false)(e: SubTree): SubTree = {
    val rec = postMap(f, applyRec) _

    val Deconstructor(es, builder) = e
    val newEs = es.map(rec)
    val newV = {
      if ((newEs zip es).exists { case (bef, aft) => aft ne bef }) {
        builder(newEs).copiedFrom(e)
      } else {
        e
      }
    }

    if (applyRec) {
      // Apply f as long as it returns Some()
      fixpoint { e : SubTree => f(e) getOrElse e } (newV)
    } else {
      f(newV) getOrElse newV
    }
  }

  /** Post-transformation of the tree using flattening methods.
    *
    * Takes a partial function of replacements.
    * Substitutes '''after''' recursing down the trees.
    *
    * Supports two modes :
    *
    *   - If applyRec is false (default), will only substitute once on each level.
    *   e.g.
    *   {{{
    *     Add(a, Minus(b, c)) with replacements: Minus(b,c) -> z, Minus(e,c) -> d, b -> e
    *   }}}
    *   will yield:
    *   {{{
    *     Add(a, Minus(e, c))
    *   }}}
    *
    *   - If applyRec is true, it will substitute multiple times on each level:
    *   e.g.
    *   {{{
    *     Add(a, Minus(b, c)) with replacements: Minus(e,c) -> d, b -> e, d -> f
    *   }}}
    *   will yield:
    *   {{{
    *     Add(a, f)
    *   }}}
    *
    * @note The mode with applyRec true can diverge if f is not well formed (i.e. not convergent)
    */
  def postFlatmap(f: SubTree => Option[Seq[SubTree]], applyRec: Boolean = false)(e: SubTree): Seq[SubTree] = {
    val rec = postFlatmap(f, applyRec) _

    val Deconstructor(es, builder) = e
    val newEss = es.map(rec)
    val newVs: Seq[SubTree] = leon.utils.SeqUtils.cartesianProduct(newEss).map { newEs =>
      if ((newEs zip es).exists { case (bef, aft) => aft ne bef }) {
        builder(newEs).copiedFrom(e)
      } else {
        e
      }
    }

    if (applyRec) {
      // Apply f as long as it returns Some()
      fixpoint { (e : Seq[SubTree]) => e.flatMap(newV => f(newV) getOrElse Seq(newV)) } (newVs)
    } else {
      newVs.flatMap((newV: SubTree) => f(newV) getOrElse Seq(newV))
    }
  }

  /** Applies functions and combines results in a generic way
    *
    * Start with an initial value, and apply functions to nodes before
    * and after the recursion in the children. Combine the results of
    * all children and apply a final function on the resulting node.
    *
    * @param pre a function applied on a node before doing a recursion in the children
    * @param post a function applied to the node built from the recursive application to
                  all children
    * @param combiner a function to combine the resulting values from all children with
                      the current node
    * @param init the initial value
    * @param expr the expression on which to apply the transform
    * @see [[simpleTransform]]
    * @see [[simplePreTransform]]
    * @see [[simplePostTransform]]
    */
  def genericTransform[C](pre:  (SubTree, C) => (SubTree, C),
                          post: (SubTree, C) => (SubTree, C),
                          combiner: (SubTree, Seq[C]) => C)(init: C)(expr: SubTree) = {

    def rec(eIn: SubTree, cIn: C): (SubTree, C) = {

      val (expr, ctx) = pre(eIn, cIn)
      val Deconstructor(es, builder) = expr
      val (newExpr, newC) = {
        val (nes, cs) = es.map{ rec(_, ctx)}.unzip
        val newE = builder(nes).copiedFrom(expr)

        (newE, combiner(newE, cs))
      }

      post(newExpr, newC)
    }

    rec(expr, init)
  }

  protected def noCombiner(e: SubTree, subCs: Seq[Unit]) = ()
  protected def noTransformer[C](e: SubTree, c: C) = (e, c)

  /** A [[genericTransform]] with the trivial combiner that returns () */
  def simpleTransform(pre: SubTree => SubTree, post: SubTree => SubTree)(tree: SubTree) = {
    val newPre  = (e: SubTree, c: Unit) => (pre(e), ())
    val newPost = (e: SubTree, c: Unit) => (post(e), ())

    genericTransform[Unit](newPre, newPost, noCombiner)(())(tree)._1
  }

  /** A [[simpleTransform]] without a post-transformation */
  def simplePreTransform(pre: SubTree => SubTree)(tree: SubTree) = {
    val newPre  = (e: SubTree, c: Unit) => (pre(e), ())

    genericTransform[Unit](newPre, (_, _), noCombiner)(())(tree)._1
  }

  /** A [[simpleTransform]] without a pre-transformation */
  def simplePostTransform(post: SubTree => SubTree)(tree: SubTree) = {
    val newPost = (e: SubTree, c: Unit) => (post(e), ())

    genericTransform[Unit]((e,c) => (e, None), newPost, noCombiner)(())(tree)._1
  }



  /** Pre-transformation of the tree, with a context value from "top-down".
    *
    * Takes a partial function of replacements.
    * Substitutes '''before''' recursing down the trees. The function returns
    * an option of the new value, as well as the new context to be used for
    * the recursion in its children. The context is "lost" when going back up,
    * so changes made by one node will not be see by its siblings.
    */
  def preMapWithContext[C](f: (SubTree, C) => (Option[SubTree], C), applyRec: Boolean = false)
                          (e: SubTree, c: C): SubTree = {

    def rec(expr: SubTree, context: C): SubTree = {

      val (newV, newCtx) = {
        if(applyRec) {
          var ctx = context
          val finalV = fixpoint{ e: SubTree => {
            val res = f(e, ctx)
            ctx = res._2
            res._1.getOrElse(e)
          }} (expr)
          (finalV, ctx)
        } else {
          val res = f(expr, context)
          (res._1.getOrElse(expr), res._2)
        }
      }

      val Deconstructor(es, builder) = newV
      val newEs = es.map(e => rec(e, newCtx))

      if ((newEs zip es).exists { case (bef, aft) => aft ne bef }) {
        builder(newEs).copiedFrom(newV)
      } else {
        newV
      }

    }

    rec(e, c)
  }

  def preFoldWithContext[C](f: (SubTree, C) => C, combiner: (SubTree, C, Seq[C]) => C)
                           (e: SubTree, c: C): C = {

    def rec(eIn: SubTree, cIn: C): C = {
      val ctx = f(eIn, cIn)
      val Deconstructor(es, _) = eIn
      val cs = es.map{ rec(_, ctx) }
      combiner(eIn, ctx, cs)
    }

    rec(e, c)
  }

  /*
   * =============
   * Auxiliary API
   * =============
   *
   * Convenient methods using the Core API.
   */

  /** Checks if the predicate holds in some sub-expression */
  def exists(matcher: SubTree => Boolean)(e: SubTree): Boolean = {
    fold[Boolean]({ (e, subs) =>  matcher(e) || subs.contains(true) } )(e)
  }

  /** Collects a set of objects from all sub-expressions */
  def collect[T](matcher: SubTree => Set[T])(e: SubTree): Set[T] = {
    fold[Set[T]]({ (e, subs) => matcher(e) ++ subs.flatten } )(e)
  }

  def collectPreorder[T](matcher: SubTree => Seq[T])(e: SubTree): Seq[T] = {
    fold[Seq[T]]({ (e, subs) => matcher(e) ++ subs.flatten } )(e)
  }

  /** Returns a set of all sub-expressions matching the predicate */
  def filter(matcher: SubTree => Boolean)(e: SubTree): Set[SubTree] = {
    collect[SubTree] { e => Set(e) filter matcher }(e)
  }

  /** Counts how many times the predicate holds in sub-expressions */
  def count(matcher: SubTree => Int)(e: SubTree): Int = {
    fold[Int]({ (e, subs) => matcher(e) + subs.sum } )(e)
  }

  /** Replaces bottom-up sub-expressions by looking up for them in a map */
  def replace(substs: Map[SubTree,SubTree], expr: SubTree) : SubTree = {
    postMap(substs.lift)(expr)
  }

  /** Replaces bottom-up sub-expressions by looking up for them in the provided order */
  def replaceSeq(substs: Seq[(SubTree, SubTree)], expr: SubTree): SubTree = {
    var res = expr
    for (s <- substs) {
      res = replace(Map(s), res)
    }
    res
  }

  /** Computes the size of a tree */
  def formulaSize(t: SubTree): Int = {
    val Deconstructor(ts, _) = t
    ts.map(formulaSize).sum + 1
  }

  /** Computes the depth of the tree */
  def depth(e: SubTree): Int = {
    fold[Int]{ (_, sub) => 1 + (0 +: sub).max }(e)
  }

  object Same {
    def unapply(tt: (SubTree, SubTree)): Option[(SubTree, SubTree)] = {
      if (tt._1.getClass == tt._2.getClass) {
        Some(tt)
      } else {
        None
      }
    }
  }

}
