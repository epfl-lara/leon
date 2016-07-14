/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars
package aspects

import Tags._

case class Tagged(tag: Tag, pos: Int, isConst: Option[Boolean]) extends Aspect {
  private val cString = isConst match {
    case Some(true) => "↓"
    case Some(false) => "↑"
    case None => "○"
  }

  /** [[isConst]] is printed as follows: ↓ for constants only, ↑ for nonconstants only,
    * ○ for anything allowed.
    */
  def asString(implicit ctx: LeonContext): String = s"#$tag$cString@$pos"

  def applyTo(lab: Label, ps: Seq[Production])(implicit ctx: LeonContext) = {

    // Tags to avoid depending on parent aspect
    val excludedTags: Set[Tag] = (tag, pos) match {
      case (Top,   _)             => Set()
      case (And,   0)             => Set(And, BooleanC)
      case (And,   1)             => Set(BooleanC)
      case (Or,    0)             => Set(Or, BooleanC)
      case (Or,    1)             => Set(BooleanC)
      case (Plus,  0)             => Set(Plus, Zero, One)
      case (Plus,  1)             => Set(Zero)
      case (Minus, 1)             => Set(Zero)
      case (Not,   _)             => Set(Not, BooleanC)
      case (Times, 0)             => Set(Times, Zero, One)
      case (Times, 1)             => Set(Zero, One)
      case (Equals,_)             => Set(Not, BooleanC)
      case (Div | Mod, 0 | 1)     => Set(Zero, One)
      case (FunCall(true, _), 0)  => Set(Constructor(true)) // Don't allow Nil().size etc.
      case _                      => Set()
    }

    def powerSet[A](t: Set[A]): Set[Set[A]] = {
      @scala.annotation.tailrec
      def pwr(t: Set[A], ps: Set[Set[A]]): Set[Set[A]] =
        if (t.isEmpty) ps
        else pwr(t.tail, ps ++ (ps map (_ + t.head)))

      pwr(t, Set(Set.empty[A]))
    }


    ps.flatMap { p =>
      val tagsValid = !(excludedTags contains p.tag)

      // If const-ness is explicit, make sure the production has similar const-ness
      val constValid = isConst match {
        case Some(b) => Tags.isConst(p.tag) == b
        case None    => true
      }

      if (constValid && tagsValid) {
        val subAspects = if (p.isTerminal || Tags.allConstArgsAllowed(p.tag)) {
          Seq(p.subTrees.indices.map { i =>
            Tagged(p.tag, i, None)
          })
        } else {
          // All positions are either forced to be const or forced to be
          // non-const. We don't want all consts though.
          val indices = p.subTrees.indices.toSet

          (powerSet(indices) - indices) map { isConst =>
            p.subTrees.indices.map { i =>
              Tagged(p.tag, i, Some(isConst(i)))
            }
          }
        }

        for (as <- subAspects) yield {
          val newSubTrees = (p.subTrees zip as).map { case (lab, a) =>
            lab.withAspect(a)
          }

          ProductionRule(newSubTrees, p.builder, p.tag, p.cost)
        }
      } else {
        Nil
      }
    }
  }
}
