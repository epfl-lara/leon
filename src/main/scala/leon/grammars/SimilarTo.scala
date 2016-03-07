/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import transformers._
import purescala.Types._
import purescala.TypeOps._
import purescala.Extractors._
import purescala.Definitions._
import purescala.Expressions._

import synthesis._

/** A grammar that generates expressions by inserting small variations in [[e]]
 * @param e The [[Expr]] to which small variations will be inserted
 */
case class SimilarTo(e: Expr, sctx: SynthesisContext, p: Problem) extends ExpressionGrammar[NonTerminal[String]] {

  val excludeFCalls = sctx.settings.functionsToIgnore

  val normalGrammar: ExpressionGrammar[NonTerminal[String]] = DepthBoundedGrammar(EmbeddedGrammar(
    Grammars.default(sctx, p, Seq(e)),
    (t: TypeTree) => NonTerminal(t, "B", None),
    (l: NonTerminal[String]) => l.getType
  ), 1)

  type L = NonTerminal[String]

  val getNext: () => Int = {
    var counter = -1
    () => {
      counter += 1
      counter
    }
  }

  private[this] var similarCache: Option[Map[L, Seq[Prod]]] = None

  def computeProductions(t: L)(implicit ctx: LeonContext): Seq[Prod] = {
    t match {
      case NonTerminal(_, "B", _) => normalGrammar.computeProductions(t)
      case _                =>

        val allSimilar = similarCache.getOrElse {
          val res = computeSimilar(e).groupBy(_._1).mapValues(_.map(_._2))
          similarCache = Some(res)
          res
        }

        allSimilar.getOrElse(t, Nil)
    }
  }

  def computeSimilar(e : Expr)(implicit ctx: LeonContext): Seq[(L, Prod)] = {

    def getLabel(t: TypeTree) = {
      val tpe = bestRealType(t)
      val c = getNext()
      NonTerminal(tpe, "G"+c)
    }

    def isCommutative(e: Expr) = e match {
      case _: Plus | _: Times => true
      case _ => false
    }

    def rec(e: Expr, gl: L): Seq[(L, Prod)] = {

      def gens(e: Expr, gl: L, subs: Seq[Expr], builder: (Seq[Expr] => Expr)): Seq[(L, Prod)] = {
        val subGls = subs.map { s => getLabel(s.getType) }

        // All the subproductions for sub gl
        val allSubs = (subs zip subGls).flatMap { case (e, gl) => rec(e, gl) }

        // Inject fix at one place
        val injectG = for ((sgl, i) <- subGls.zipWithIndex) yield {
          gl -> nonTerminal(Seq(sgl), { case Seq(ge) => builder(subs.updated(i, ge)) } )
        }

        val swaps = if (subs.size > 1 && !isCommutative(e)) {
          (for (i <- subs.indices;
                j <- i+1 until subs.size) yield {

            if (subs(i).getType == subs(j).getType) {
              val swapSubs = subs.updated(i, subs(j)).updated(j, subs(i))
              Some(gl -> terminal(builder(swapSubs)))
            } else {
              None
            }
          }).flatten
        } else {
          Nil
        }

        allSubs ++ injectG ++ swaps
      }

      def cegis(gl: L): Seq[(L, Prod)] = {
        normalGrammar.getProductions(gl).map(gl -> _)
      }

      def int32Variations(gl: L, e : Expr): Seq[(L, Prod)] = {
        Seq(
          gl -> terminal(BVMinus(e, IntLiteral(1))),
          gl -> terminal(BVPlus (e, IntLiteral(1)))
        )
      }

      def intVariations(gl: L, e : Expr): Seq[(L, Prod)] = {
        Seq(
          gl -> terminal(Minus(e, InfiniteIntegerLiteral(1))),
          gl -> terminal(Plus (e, InfiniteIntegerLiteral(1)))
        )
      }

      // Find neighbor case classes that are compatible with the arguments:
      // Turns And(e1, e2) into Or(e1, e2)...
      def ccVariations(gl: L, cc: CaseClass): Seq[(L, Prod)] = {
        val CaseClass(cct, args) = cc

        val neighbors = cct.root.knownCCDescendants diff Seq(cct)

        for (scct <- neighbors if scct.fieldsTypes == cct.fieldsTypes) yield {
          gl -> terminal(CaseClass(scct, args))
        }
      }

      val funFilter = (fd: FunDef) => fd.isSynthetic || (excludeFCalls contains fd)
      val subs: Seq[(L, Prod)] = e match {
        
        case _: Terminal | _: Let | _: LetDef | _: MatchExpr =>
          gens(e, gl, Nil, { _ => e }) ++ cegis(gl)

        case cc @ CaseClass(cct, exprs) =>
          gens(e, gl, exprs, { case ss => CaseClass(cct, ss) }) ++ ccVariations(gl, cc)

        case FunctionInvocation(TypedFunDef(fd, _), _) if funFilter(fd) =>
          // We allow only exact call, and/or cegis extensions
          /*Seq(el -> Generator[L, Expr](Nil, { _ => e })) ++*/ cegis(gl)

        case Operator(subs, builder) =>
          gens(e, gl, subs, { case ss => builder(ss) })
      }

      val terminalsMatching = p.as.collect {
        case IsTyped(term, tpe) if tpe == gl.getType && Variable(term) != e =>
          gl -> terminal(Variable(term))
      }

      val variations = e.getType match {
        case IntegerType => intVariations(gl, e)
        case Int32Type => int32Variations(gl, e)
        case _ => Nil
      }

      subs ++ terminalsMatching ++ variations
    }

    val gl = getLabel(e.getType)

    val res = rec(e, gl)

    //for ((t, g) <- res) {
    //  val subs = g.subTrees.map { t => FreshIdentifier(t.asString, t.getType).toVariable}
    //  val gen = g.builder(subs)

    //  println(f"$t%30s ::= "+gen)
    //}
    res
  }
}
