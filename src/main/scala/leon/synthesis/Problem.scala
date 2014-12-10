/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

import leon.purescala.Trees._
import leon.purescala.Definitions._
import leon.purescala.TreeOps._
import leon.purescala.TypeTrees.TypeTree
import leon.purescala.Common._
import leon.purescala.Constructors._
import leon.purescala.Extractors._

// Defines a synthesis triple of the form:
// ⟦ as ⟨ ws && pc | phi ⟩ xs ⟧
case class Problem(as: List[Identifier], ws: Expr, pc: Expr, phi: Expr, xs: List[Identifier]) {

  override def toString = {
    val pcws = and(ws, pc)
    "⟦ "+as.mkString(";")+", "+(if (pcws != BooleanLiteral(true)) pcws+" ≺ " else "")+" ⟨ "+phi+" ⟩ "+xs.mkString(";")+" ⟧ "
  }

  def getTests(sctx: SynthesisContext): Seq[Example] = {
    import purescala.Extractors._
    import evaluators._

    val predicates = and(pc, phi)

    val ev = new DefaultEvaluator(sctx.context, sctx.program)

    def isValidExample(ex: Example): Boolean = {
      val (mapping, cond) = ex match {
        case io: InOutExample =>
          (Map((as zip io.ins) ++ (xs zip io.outs): _*), And(pc, phi))
        case i =>
          ((as zip i.ins).toMap, pc)
      }

      ev.eval(cond, mapping) match {
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
  

    def toIOExamples(in: Expr, out : Expr, cs : MatchCase) : Seq[(Expr,Expr)] = {
      import utils.ExpressionGrammars.ValueGrammar
      import leon.utils.StreamUtils.cartesianProduct
      import bonsai._
      import bonsai.enumerators._

      val examplesPerCase = 5
     
      def doSubstitute(subs : Seq[(Identifier, Expr)], e : Expr) = 
        subs.foldLeft(e) { 
          case (from, (id, to)) => replaceFromIDs(Map(id -> to), from)
        }

      if (cs.rhs == out) {
        // The trivial example
        Seq()
      } else {
        // The pattern as expression (input expression)(may contain free variables)
        val (pattExpr, ieMap) = patternToExpression(cs.pattern, in.getType)
        val freeVars = variablesOf(pattExpr).toSeq
        if (freeVars.isEmpty) {
          // The input contains no free vars. Trivially return input-output pair
          Seq((pattExpr, doSubstitute(ieMap,cs.rhs)))
        } else {
          // If the input contains free variables, it does not provide concrete examples. 
          // We will instantiate them according to a simple grammar to get them.
          val enum = new MemoizedEnumerator[TypeTree, Expr](ValueGrammar.getProductions _)
          val types = freeVars.map{ _.getType }
          val typesWithValues = types.map { tp => (tp, enum.iterator(tp).toStream) }.toMap
          val values = freeVars map { v => typesWithValues(v.getType) }
          val instantiations = cartesianProduct(values) map { freeVars.zip(_).toMap }
          if (false && cs.optGuard.isDefined){
            // TODO: Filter examples by guard
            Seq()
          } else {
            instantiations.map { inst =>
              (replaceFromIDs(inst, pattExpr), replaceFromIDs(inst, doSubstitute(ieMap, cs.rhs)))  
            }.take(examplesPerCase)
          }
          
          
        }
        
      }
    }

    val evaluator = new DefaultEvaluator(sctx.context, sctx.program)

    val testClusters = collect[Map[Identifier, Expr]] {

      //case FunctionInvocation(tfd, List(in, out, FiniteMap(inouts))) if tfd.id.name == "passes" =>
      case p@Passes(ins, out, cases) =>
        
        val ioPairs = cases flatMap { toIOExamples(ins,out,_) }
        val infos = extractIds(Tuple(Seq(ins,out)))
        val exs   = ioPairs.map{ case (i, o) =>
          val test = Tuple(Seq(i, o))
          val ids = variablesOf(test)
          evaluator.eval(test, ids.map { (i: Identifier) => i -> i.toVariable }.toMap) match {
            case EvaluationResults.Successful(res) => res
            case _ =>
              test
          }
        }

        // Check whether we can extract all ids from example
        val results = exs.collect { case e if infos.forall(_._2.isDefinedAt(e)) =>
          infos.map{ case (id, f) => id -> f(e) }.toMap
        }

        results.toSet

      case _ =>
        Set()
    }(predicates)

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
    for (t <- testClusters) {
      consolidated += t

      consolidated = consolidated.map { c =>
        mergeTest(c, t)
      }
    }

    // Finally, we keep complete tests covering all as++xs
    val allIds  = (as ++ xs).toSet
    val insIds  = as.toSet
    val outsIds = xs.toSet

    val examples = consolidated.toSeq.flatMap { t =>
      val ids = t.keySet
      if ((ids & allIds) == allIds) {
        Some(InOutExample(as.map(t), xs.map(t)))
      } else if ((ids & insIds) == insIds) {
        Some(InExample(as.map(t)))
      } else {
        None
      }
    }

    examples.filter(isValidExample)
  }
}

object Problem {
  def fromChoose(ch: Choose, pc: Expr = BooleanLiteral(true)): Problem = {
    val xs = ch.vars
    val phi = simplifyLets(ch.pred)
    val as = (variablesOf(And(pc, phi))--xs).toList

    val TopLevelAnds(clauses) = pc

    val (pcs, wss) = clauses.partition {
      case FunctionInvocation(TypedFunDef(fd, _), _) if fd.annotations("witness") => false
      case _ => true
    }

    Problem(as, andJoin(wss), andJoin(pcs), phi, xs)
  }
}
