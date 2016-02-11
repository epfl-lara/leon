/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars
package transformers

import leon.purescala.Types.Typed
import Tags._

/** Adds to a nonterminal information about about the tag of its parent's [[leon.grammars.ProductionRule.tag]]
  * and additional information.
  * 
  * @param underlying The underlying nonterminal
  * @param tag The tag of the parent of this nonterminal
  * @param pos The index of this nonterminal in its father's production rule
  * @param isConst Whether this nonterminal is obliged to generate/not generate constants.
  *
  */
case class TaggedNonTerm[T <: Typed](underlying: T, tag: Tag, pos: Int, isConst: Option[Boolean]) extends Typed {
  val getType = underlying.getType

  private val cString = isConst match {
    case Some(true) => "↓"
    case Some(false) => "↑"
    case None => "○"
  }

  /** [[isConst]] is printed as follows: ↓ for constants only, ↑ for nonconstants only,
    * ○ for anything allowed.
    */
  override def asString(implicit ctx: LeonContext): String = s"$underlying%$tag@$pos$cString"
}

/** Constraints a grammar to reduce redundancy by utilizing information provided by the [[TaggedNonTerm]].
  *
  * 1) In case of associative operations, right associativity is enforced.
  * 2) Does not generate
  *    - neutral and absorbing elements (incl. boolean equality)
  *    - nested negations
  * 3) Excludes method calls on nullary case objects, e.g. Nil().size
  * 4) Enforces that no constant trees are generated (and recursively for each subtree)
  *
  * @param g The underlying untagged grammar
  */
case class TaggedGrammar[T <: Typed](g: ExpressionGrammar[T]) extends ExpressionGrammar[TaggedNonTerm[T]] {

  private def exclude(tag: Tag, pos: Int): Set[Tag] = (tag, pos) match {
    case (Top,   _) => Set()
    case (And,   0) => Set(And, BooleanC)
    case (And,   1) => Set(BooleanC)
    case (Or,    0) => Set(Or, BooleanC)
    case (Or,    1) => Set(BooleanC)
    case (Plus,  0) => Set(Plus, Zero, One)
    case (Plus,  1) => Set(Zero)
    case (Minus, 1) => Set(Zero)
    case (Not,   _) => Set(Not, BooleanC)
    case (Times, 0) => Set(Times, Zero, One)
    case (Times, 1) => Set(Zero, One)
    case (Equals,_) => Set(Not, BooleanC)
    case (Div | Mod, 0 | 1) => Set(Zero, One)
    case (FunCall(true, _), 0) => Set(Constructor(true)) // Don't allow Nil().size etc.
    case _ => Set()
  }

  def computeProductions(t: TaggedNonTerm[T])(implicit ctx: LeonContext): Seq[Prod] = {

    // Point (4) for this level
    val constFilter: g.Prod => Boolean = t.isConst match {
      case Some(b) =>
        innerGen => isConst(innerGen.tag) == b
      case None =>
        _ => true
    }

    g.computeProductions(t.underlying)
      // Include only constants iff constants are forced, only non-constants iff they are forced
      .filter(constFilter)
      // Points (1), (2). (3)
      .filterNot { innerGen => exclude(t.tag, t.pos)(innerGen.tag) }
      .flatMap   { innerGen =>

        def nt(isConst: Int => Option[Boolean]) = innerGen.copy(
          subTrees = innerGen.subTrees.zipWithIndex.map {
            case (t, pos) => TaggedNonTerm(t, innerGen.tag, pos, isConst(pos))
          }
        )

        def powerSet[A](t: Set[A]): Set[Set[A]] = {
          @scala.annotation.tailrec
          def pwr(t: Set[A], ps: Set[Set[A]]): Set[Set[A]] =
            if (t.isEmpty) ps
            else pwr(t.tail, ps ++ (ps map (_ + t.head)))

          pwr(t, Set(Set.empty[A]))
        }

        // Allow constants everywhere if this is allowed, otherwise demand at least 1 variable.
        // Aka. tag subTrees correctly so point (4) is enforced in the lower level
        // (also, make sure we treat terminals correctly).
        if (innerGen.isTerminal || allConstArgsAllowed(innerGen.tag)) {
          Seq(nt(_ => None))
        } else {
          val indices = innerGen.subTrees.indices.toSet
          (powerSet(indices) - indices) map (indices => nt(x => Some(indices(x))))
        }
      }
  }

}
