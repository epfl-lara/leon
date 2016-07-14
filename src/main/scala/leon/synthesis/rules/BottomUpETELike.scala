/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.Types._
import purescala.Constructors._

import evaluators._
import codegen.CodeGenParams
import leon.grammars._
import leon.utils.SeqUtils._

/** A common base for all clases implementing Bottom-up Example-guided Term Exploration */
abstract class BottomUpETELike(name: String) extends Rule(name) {
  case class ETEParams(
    grammar: ExpressionGrammar,
    maxExpands: Int
  )

  type Signature = Vector[Expr]

  case class EqClass(sig: Signature, cand: Expr) {
    def asString(implicit ctx: LeonContext): String = {
      f"${cand.asString}%-50s <- "+debugSig(sig)
    }
  }

  def debugSig(sig: Signature)(implicit ctx: LeonContext) = {
    val hash = Integer.toHexString(sig.hashCode)

    hash+": "+sig.map(_.asString).mkString(" ,  ")
  }

  def getParams(sctx: SynthesisContext, p: Problem): ETEParams

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val inOutExamples = p.qeb.examples collect {
      case io: InOutExample => io
    }

    if (inOutExamples.nonEmpty) {
      List(new RuleInstantiation(this.name) {
        def apply(hctx: SearchContext): RuleApplication = {
          implicit val ci = hctx
          val params = getParams(hctx, p)
          val grammar = params.grammar

          val examples = p.qebFiltered.examples.collect { case io: InOutExample => io }.toVector

          if (examples.nonEmpty) {

            ci.reporter.debug(ExamplesBank(examples, Nil).asString("Tests"))

            val evalParams = CodeGenParams.default.copy(maxFunctionInvocations = 2000)
            val evaluator  = new DualEvaluator(hctx, hctx.program, params = evalParams)

            val examplesEnvs = examples.map { case InOutExample(is, os) => (p.as zip is).toMap }
            val targetSign   = examples.map { case InOutExample(_, os) => tupleWrap(os) }

            val targetType = tupleTypeWrap(p.xs.map(_.getType))

            var classes = Map[TypeTree, Map[Signature, EqClass]]()
            var newClasses = classes

            def debugClasses() = {
              for ((tpe, cs) <- classes) {
                println(s"===== ${tpe.asString} =====")
                for (c <- cs.values) {
                  println(s" - ${c.asString}")
                }
              }
            }

            def findTargetSign(classes: Map[Signature, EqClass]): Option[EqClass] = {
              classes.get(targetSign)
            }

            def expandAll(): Option[EqClass] = {
              //println("#"*80)
              //debugClasses()
              //println("#"*80)

              for (tpe <- classes.keys) {
                expand(tpe)
                if (tpe == targetType) {
                  findTargetSign(newClasses(tpe)) match {
                    case Some(cl) => return Some(cl)
                    case None =>
                  }
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
                }

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
    } else {
      Nil
    }
  }
}
