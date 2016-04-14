/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import Witnesses.Hint
import purescala.Expressions._
import purescala.Common._
import purescala.Types._
import purescala.ExprOps.simplePostTransform
import purescala.Constructors._
import purescala.Extractors.LetPattern

/** Rule for detupling input variables, to be able to use their sub-expressions. For example, the input variable:
  * {{{d: Cons(head: Int, tail: List)}}}
  * will create the following input variables
  * {{{head42: Int, tail57: List}}}
  * Recomposition is available.
  */
case object DetupleInput extends NormalizingRule("Detuple In") {

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    /** Returns true if this identifier is a tuple or a case class */
    def isDecomposable(id: Identifier) = id.getType match {
      case CaseClassType(t, _) if !t.isAbstract => true
      case TupleType(ts) => true
      case _ => false
    }

    /* Decomposes a decomposable input identifier (eg of type Tuple or case class)
     * into a list of fresh typed identifiers, the tuple of these new identifiers,
     * and the mapping of those identifiers to their respective expressions.
     */
    def decompose(id: Identifier): (List[Identifier], Expr, Expr => Seq[Expr]) = id.getType match {
      case cct @ CaseClassType(ccd, _) if !ccd.isAbstract =>
        val newIds = cct.fields.map{ vd => FreshIdentifier(vd.id.name, vd.getType, true) }

        val tMap: (Expr => Seq[Expr]) = {
          case CaseClass(ccd, fields) => fields
        }

        (newIds.toList, CaseClass(cct, newIds.map(Variable)), tMap)

      case TupleType(ts) =>
        val newIds = ts.zipWithIndex.map{ case (t, i) => FreshIdentifier(id.name+"_"+(i+1), t, true) }

        val tMap: (Expr => Seq[Expr]) = {
          case Tuple(fields) => fields
        }

        (newIds.toList, tupleWrap(newIds.map(Variable)), tMap)

      case _ => sys.error("woot")
    }

    if (p.as.exists(isDecomposable)) {
      var subProblem = p.phi
      var subPc      = p.pc
      var subWs      = p.ws
      var hints: Seq[Expr] = Nil
      var patterns = List[(Identifier, Pattern)]()
      var revMap = Map[Expr, Expr]().withDefault((e: Expr) => e)

      var ebMapInfo = Map[Identifier, Expr => Seq[Expr]]()

      val subAs = p.as.map { a =>
        if (isDecomposable(a)) {
          val (newIds, expr, tMap) = decompose(a)

          subProblem = subst(a -> expr, subProblem)
          subPc      = subPc map (subst(a -> expr, _))
          subWs      = subst(a -> expr, subWs)
          revMap     += expr -> Variable(a)
          hints      +:= Hint(expr)

          val patts = newIds map (id => WildcardPattern(Some(id)))

          patterns +:= ((
            a,
            a.getType match {
              case TupleType(_) =>
                TuplePattern(None, patts)
              case cct: CaseClassType =>
                CaseClassPattern(None, cct, patts)
            }
          ))

          ebMapInfo += a -> tMap

          newIds
        } else {
          List(a)
        }
      }

      val eb = p.qeb.mapIns { info =>
        List(info.flatMap { case (id, v) =>
          ebMapInfo.get(id) match {
            case Some(m) =>
              m(v)
            case None =>
              List(v)
          }
        })
      }

      val newAs = subAs.flatten

      val (as, patts) = patterns.unzip

      val sub = Problem(newAs, subWs, subPc, subProblem, p.xs, eb).withWs(hints)

      val s = { (e: Expr) =>
        val body = simplePostTransform(revMap)(e)
        (patts zip as).foldRight(body) { case ((patt, a), bd) =>
          LetPattern(patt, a.toVariable, bd)
        }
      }
     
      Some(decomp(List(sub), forwardMap(s), s"Detuple ${as.mkString(", ")}"))
    } else {
      None
    }
  }
}
