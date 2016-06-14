/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.Types._
import purescala.Constructors._

import datagen._
import evaluators._
import codegen.CodeGenParams
import leon.grammars._
import leon.grammars.aspects.Sized
import leon.utils.GrowableIterable
import leon.utils.SeqUtils._

import scala.collection.mutable.{HashMap => MutableMap}

import bonsai.enumerators._




abstract class BottomUpTEGISLike(name: String) extends Rule(name) {
  case class TegisParams(
    grammar: ExpressionGrammar,
    maxExpands: Int
  )

  type Signature = Vector[Expr]

  case class EqClass(sig: Signature, cand: Expr) {
    def asString(target: Option[Signature] = None)(implicit ctx: LeonContext): String = {

      val hash = Integer.toHexString(sig.hashCode)

      val isMatch = Some(sig) == target

      val okSign = if (isMatch) "OK" else "  "

      f"${cand.asString}%-50s <- "+okSign+" "+debugSig(sig)
    }
  }

  def debugSig(sig: Signature)(implicit ctx: LeonContext) = {
    val hash = Integer.toHexString(sig.hashCode)

    hash+": "+sig.map(_.asString).mkString(" ,  ")
  }

  def getParams(sctx: SynthesisContext, p: Problem): TegisParams

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {

    List(new RuleInstantiation(this.name) {
      def apply(hctx: SearchContext): RuleApplication = {
        implicit val ci = hctx
        val params = getParams(hctx, p)
        val grammar = params.grammar

        val nTests = if (p.pc.isEmpty) 50 else 20

        val examples = p.qebFiltered.examples.collect { case io: InOutExample => io }.toVector

        if (examples.nonEmpty) {
          ci.reporter.debug(ExamplesBank(examples, Nil).asString("Tests"))

          val evalParams = CodeGenParams.default.copy(maxFunctionInvocations = 2000)
          val evaluator  = new DualEvaluator(hctx, hctx.program, params = evalParams)

          val examplesEnvs = examples.map { case InOutExample(is, os) => (p.as zip is).toMap }
          val targetSign   = examples.map { case InOutExample(_, os) => tupleWrap(os) }

          //println("Looking for "+debugSig(targetSign))

          val enum = new MemoizedEnumerator[Label, Expr, ProductionRule[Label, Expr]](grammar.getProductions)

          val targetType = tupleTypeWrap(p.xs.map(_.getType))

          val timers = hctx.timers.synthesis.rules.bottomuptegis

          var classes = Map[TypeTree, Map[Signature, EqClass]]()
          var newClasses = classes

          def debugClasses() = {
            for ((tpe, cs) <- classes) {
              println(s"===== ${tpe.asString} =====")
              for (c <- cs.values) {
                println(s" - ${c.asString(Some(targetSign))}")
              }
            }
          }

          def expandAll(): Option[EqClass] = {
            //println("#"*80)
            //debugClasses()
            //println("#"*80)

            for (tpe <- classes.keys) {
              expand(tpe)
              if ((tpe == targetType) && (newClasses(tpe) contains targetSign)) {
                return Some(newClasses(tpe)(targetSign))
              }
            }

            classes = newClasses


            //println("@"*80)
            //debugClasses()
            //println("@"*80)
            None
          }

          def registerClasses(tpe: TypeTree, cs: Seq[EqClass]) = {
            var existings = newClasses.getOrElse(tpe, Map())

            for (c @ EqClass(sig, cand) <- cs) {
              if (!(existings contains sig)) {
                existings += sig -> c
              }
            }

            newClasses += tpe -> existings
          }

          def expand(tpe: TypeTree) = {
            val label = Label(tpe)

            val cs = grammar.getProductions(label).collect {
              case ProductionRule(subLabels, builder, _, _) if subLabels.nonEmpty =>
                compose(subLabels.map(sl => getClasses(sl.getType)), builder)
            }.flatten

            registerClasses(tpe, cs)
          }

          def classBuilder(argss: Seq[EqClass], builder: Seq[Expr] => Expr): Option[EqClass] = {
            try {
              val sig = examplesEnvs.zipWithIndex.map { case (env, i) =>
                val expr = builder(argss.map(_.sig(i)))
                evaluator.eval(expr, env).result.get
              }.toVector

              val cand = builder(argss.map(_.cand))

              Some(EqClass(sig, cand))
            } catch {
              case _: RuntimeException => None
            }
          }

          def compose(sigss: Seq[Seq[EqClass]], builder: Seq[Expr] => Expr): Seq[EqClass] = {
            cartesianProduct(sigss).flatMap { asigs =>
              classBuilder(asigs, builder)
            }
          }

          def getClasses(tpe: TypeTree): Seq[EqClass] = {
            classes.get(tpe) match {
              case Some(cls) =>
                cls.values.toSeq
              case None =>
                initClass(tpe)
            }
          }

          def initClass(tpe: TypeTree): Seq[EqClass] = {
            classes += tpe -> Map()

            val prods = grammar.getProductions(Label(tpe))

            val existsTerminals = prods.exists(_.subTrees.isEmpty)

            val res = grammar.getProductions(Label(tpe)).collect {
              case ProductionRule(subLabels, builder, _, _) if !existsTerminals || subLabels.isEmpty =>
                compose(subLabels.map(sl => getClasses(sl.getType)), builder)
            }.flatten

            registerClasses(tpe, res)
            classes += tpe -> newClasses(tpe)

            res
          }

          initClass(targetType)

          val sols = (1 to params.maxExpands).toStream.flatMap(i => expandAll().map(_.cand)).map { expr =>
            Solution(BooleanLiteral(true), Set(), expr, isTrusted = p.isTestBased)
          }
          RuleClosed(sols)
        } else {
          hctx.reporter.debug("No test available")
          RuleFailed()
        }
      }
    })
  }
}
