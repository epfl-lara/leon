/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.Common._

// Defines a synthesis triple of the form:
// ⟦ as ⟨ C | phi ⟩ xs ⟧
case class Problem(as: List[Identifier], pc: Expr, phi: Expr, xs: List[Identifier]) {
  override def toString = "⟦ "+as.mkString(";")+", "+(if (pc != BooleanLiteral(true)) pc+" ≺ " else "")+" ⟨ "+phi+" ⟩ "+xs.mkString(";")+" ⟧ "

  def getTests(sctx: SynthesisContext): Seq[InOutExample] = {
    import purescala.Extractors._
    import evaluators._

    val TopLevelAnds(predicates) = And(pc, phi)

    val ev = new DefaultEvaluator(sctx.context, sctx.program)

    def isValidExample(ex: InOutExample): Boolean = {
      val mapping = Map((as zip ex.ins) ++ (xs zip ex.outs): _*)

      ev.eval(And(pc, phi), mapping) match {
        case EvaluationResults.Successful(BooleanLiteral(true)) => true
        case _ => false
      }
    }

    // Returns a list of identifiers, and extractors
    def andThen(pf1: PartialFunction[Expr, Expr], pf2: PartialFunction[Expr, Expr]): PartialFunction[Expr, Expr] = {
      Function.unlift(pf1.lift(_) flatMap pf2.lift)
    }

    /**
     * Extract ids in ins/outs args, and compute corresponding extractors for values map
     *
     * Examples:
     * (a,b) =>
     *     a -> _.1
     *     b -> _.2
     *
     * Cons(a, Cons(b, c)) =>
     *     a -> _.head
     *     b -> _.tail.head
     *     c -> _.tail.tail
     */
    def extractIds(e: Expr): Seq[(Identifier, PartialFunction[Expr, Expr])] = e match {
      case Variable(id) =>
        List((id, { case e => e }))
      case Tuple(vs) =>
        vs.map(extractIds).zipWithIndex.flatMap{ case (ids, i) =>
          ids.map{ case (id, e) =>
            (id, andThen({ case Tuple(vs) => vs(i) }, e))
          }
        }
      case CaseClass(cct, args) =>
        args.map(extractIds).zipWithIndex.flatMap { case (ids, i) =>
          ids.map{ case (id, e) =>
            (id, andThen({ case CaseClass(cct2, vs) if cct2 == cct => vs(i) } ,e))
          }
        }

      case _ =>
        sctx.reporter.warning("Unnexpected pattern in test-ids extraction: "+e)
        Nil
    }

    def exprToIds(e: Expr): List[Identifier] = e match {
      case Variable(i) => List(i)
      case Tuple(is) => is.collect { case Variable(i) => i }.toList
      case _ => Nil
    }

    val testClusters = predicates.collect {
      case FunctionInvocation(tfd, List(in, out, FiniteMap(inouts))) if tfd.id.name == "passes" =>
        val infos = extractIds(Tuple(Seq(in, out)))
        val exs   = inouts.map{ case (i, o) => Tuple(Seq(i, o)) }

        // Check whether we can extract all ids from example
        val results = exs.collect { case e if infos.forall(_._2.isDefinedAt(e)) =>
          infos.map{ case (id, f) => id -> f(e) }.toMap
        }

        results
    }

    /**
     * we now need to consolidate different clusters of compatible tests together
     * t1: a->1, c->3
     * t2: a->1, b->4
     *   => a->1, b->4, c->3
     */

    def isCompatible(m1: Map[Identifier, Expr], m2: Map[Identifier, Expr]) = {
      val ks = m1.keySet & m2.keySet
      ks.nonEmpty && ks.map(m1) == ks.map(m2)
    }

    def mergeTest(m1: Map[Identifier, Expr], m2: Map[Identifier, Expr]) = {
      if (!isCompatible(m1, m2)) {
        m1
      } else {
        m1 ++ m2
      }
    }

    var consolidated = Set[Map[Identifier, Expr]]()
    for (ts <- testClusters; t <- ts) {
      consolidated += t

      consolidated = consolidated.map { c =>
        mergeTest(c, t)
      }
    }

    // Finally, we keep complete tests covering all as++xs
    val requiredIds = (as ++ xs).toSet
    val complete = consolidated.filter{ t => (t.keySet & requiredIds) == requiredIds }

    complete.toSeq.map { m =>
      InOutExample(as.map(m), xs.map(m))
    }.filter(isValidExample)
  }
}

object Problem {
  def fromChoose(ch: Choose, pc: Expr = BooleanLiteral(true)): Problem = {
    val xs = ch.vars
    val phi = ch.pred
    val as = (variablesOf(And(pc, phi))--xs).toList

    Problem(as, pc, phi, xs)
  }
}
