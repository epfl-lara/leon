/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars
package aspects

import Tags._

case class Tagged(tag: Tag, pos: Int, isConst: Option[Boolean]) extends Aspect(1000) {
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

    def powerSet[A](t: Set[A]): Set[Set[A]] = {
      @scala.annotation.tailrec
      def pwr(t: Set[A], ps: Set[Set[A]]): Set[Set[A]] =
        if (t.isEmpty) ps
        else pwr(t.tail, ps ++ (ps map (_ + t.head)))

      pwr(t, Set(Set.empty[A]))
    }


    ps.flatMap { p =>
      val tagsValid = !(excludedTags(tag, pos) contains p.tag)

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

          ProductionRule(newSubTrees, p.builder, p.tag, p.cost, p.logProb)
        }
      } else {
        Nil
      }
    }
  }
}
