package leon
package synthesis
package utils

import bonsai._

import Helpers._

import purescala.Trees._
import purescala.Common._
import purescala.Definitions._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.DefOps._
import purescala.TypeTreeOps._
import purescala.Extractors._
import purescala.ScalaPrinter
import scala.language.implicitConversions

import scala.collection.mutable.{HashMap => MutableMap}

abstract class ExpressionGrammar[T <% Typed] {
  type Gen = Generator[T, Expr]

  private[this] val cache = new MutableMap[T, Seq[Gen]]()

  def getProductions(t: T): Seq[Gen] = {
    cache.getOrElse(t, {
      val res = computeProductions(t)
      cache += t -> res
      res
    })
  }

  def computeProductions(t: T): Seq[Gen]

  final def ||(that: ExpressionGrammar[T]): ExpressionGrammar[T] = {
    ExpressionGrammars.Or(Seq(this, that))
  }


  final def printProductions(printer: String => Unit) {
    for ((t, gs) <- cache; g <- gs) {
      val subs = g.subTrees.map { t => FreshIdentifier(t.toString).setType(t.getType).toVariable}
      val gen = g.builder(subs)

      printer(f"$t%30s ::= "+gen)
    }
  }
}

object ExpressionGrammars {

  case class Or[T <% Typed](gs: Seq[ExpressionGrammar[T]]) extends ExpressionGrammar[T] {
    val subGrammars: Seq[ExpressionGrammar[T]] = gs.flatMap {
      case o: Or[T] => o.subGrammars
      case g => Seq(g)
    }

    def computeProductions(t: T): Seq[Gen] =
      subGrammars.flatMap(_.getProductions(t))
  }

  case class Empty[T <% Typed]() extends ExpressionGrammar[T] {
    def computeProductions(t: T): Seq[Gen] = Nil
  }

  case object BaseGrammar extends ExpressionGrammar[TypeTree] {
    def computeProductions(t: TypeTree): Seq[Gen] = t match {
      case BooleanType =>
        List(
          Generator(Nil, { _ => BooleanLiteral(true) }),
          Generator(Nil, { _ => BooleanLiteral(false) })
        )
      case Int32Type =>
        List(
          Generator(Nil, { _ => IntLiteral(0) }),
          Generator(Nil, { _ => IntLiteral(1) }),
          Generator(List(Int32Type, Int32Type), { case Seq(a,b) => Plus(a, b) }),
          Generator(List(Int32Type, Int32Type), { case Seq(a,b) => Minus(a, b) }),
          Generator(List(Int32Type, Int32Type), { case Seq(a,b) => Times(a, b) })
        )

      case tp@TypeParameter(_) =>
        for (ind <- (1 to 3).toList) yield
          Generator[TypeTree, Expr](Nil, { _ => GenericValue(tp, ind) } )

      case TupleType(stps) =>
        List(Generator(stps, { sub => Tuple(sub) }))

      case cct: CaseClassType =>
        List(
          Generator(cct.fields.map(_.getType), { case rs => CaseClass(cct, rs)} )
        )

      case act: AbstractClassType =>
        act.knownCCDescendents.map { cct =>
          Generator[TypeTree, Expr](cct.fields.map(_.getType), { case rs => CaseClass(cct, rs)} )
        }

      case st @ SetType(base) =>
        List(
          Generator(List(base),   { case elems     => FiniteSet(elems.toSet).setType(st) }),
          Generator(List(st, st), { case Seq(a, b) => SetUnion(a, b) }),
          Generator(List(st, st), { case Seq(a, b) => SetIntersection(a, b) }),
          Generator(List(st, st), { case Seq(a, b) => SetDifference(a, b) })
        )

      case _ =>
        Nil
    }
  }

  case object ValueGrammar extends ExpressionGrammar[TypeTree] {
    def computeProductions(t: TypeTree): Seq[Gen] = t match {
      case BooleanType =>
        List(
          Generator(Nil, { _ => BooleanLiteral(true) }),
          Generator(Nil, { _ => BooleanLiteral(false) })
        )
      case Int32Type =>
        List(
          Generator(Nil, { _ => IntLiteral(0) }),
          Generator(Nil, { _ => IntLiteral(1) }),
          Generator(Nil, { _ => IntLiteral(-1) })
        )

      case tp@TypeParameter(_) =>
        for (ind <- (1 to 3).toList) yield
          Generator[TypeTree, Expr](Nil, { _ => GenericValue(tp, ind) } )

      case TupleType(stps) =>
        List(Generator(stps, { sub => Tuple(sub) }))

      case cct: CaseClassType =>
        List(
          Generator(cct.fields.map(_.getType), { case rs => CaseClass(cct, rs)} )
        )

      case act: AbstractClassType =>
        act.knownCCDescendents.map { cct =>
          Generator[TypeTree, Expr](cct.fields.map(_.getType), { case rs => CaseClass(cct, rs)} )
        }

      case st @ SetType(base) =>
        List(
          Generator(List(base),       { case elems => FiniteSet(elems.toSet).setType(st) }),
          Generator(List(base, base), { case elems => FiniteSet(elems.toSet).setType(st) })
        )

      case _ =>
        Nil
    }
  }

  case class OneOf(inputs: Seq[Expr]) extends ExpressionGrammar[TypeTree] {
    def computeProductions(t: TypeTree): Seq[Gen] = {
      inputs.collect {
        case i if isSubtypeOf(i.getType, t) => Generator[TypeTree, Expr](Nil, { _ => i })
      }
    }
  }

  case class Label[T](t: TypeTree, l: T) extends Typed {
    def getType = t

    override def toString = t.toString+"@"+l
  }

  case class SimilarTo(e: Expr, terminals: Set[Expr] = Set(), sctx: SynthesisContext, p: Problem) extends ExpressionGrammar[Label[String]] {

    val excludeFCalls = sctx.settings.functionsToIgnore
    
    val normalGrammar = EmbeddedGrammar(
        BaseGrammar ||
        FunctionCalls(sctx.program, sctx.functionContext, p.as.map(_.getType), excludeFCalls) ||
        SafeRecCalls(sctx.program, p.ws, p.pc),
      { (t: TypeTree)      => Label(t, "B")},
      { (l: Label[String]) => l.getType }
    )     
    
    type L = Label[String]

    private var counter = -1;
    def getNext(): Int = {
      counter += 1;
      counter
    }

    lazy val allSimilar = computeSimilar(e).groupBy(_._1).mapValues(_.map(_._2))

    def computeProductions(t: L): Seq[Gen] = {
      t match {
        case Label(_, "B") => normalGrammar.computeProductions(t)
        case _ => allSimilar.getOrElse(t, Nil)
      }
    }

    def computeSimilar(e : Expr) : Seq[(L, Gen)] = {

      def getLabelPair(t: TypeTree) = {
        val tpe = bestRealType(t)
        val c = getNext
        (Label(tpe, "E"+c), Label(tpe, "G"+c))
      }

      def isCommutative(e: Expr) = e match {
        case _: Plus | _: Times => true
        case _ => false
      }

      def rec(e: Expr, el: L, gl: L): Seq[(L, Gen)] = {

        def gens(e: Expr, el: L, gl: L, subs: Seq[Expr], builder: (Seq[Expr] => Expr)): Seq[(L, Gen)] = {
          val subLabels = subs.map { s => getLabelPair(s.getType) }
          val (subEls, subGls) = subLabels.unzip

          // All the subproductions for sub el/gl
          val allSubs = (subs zip subLabels).flatMap { case (e, (el, gl)) => rec(e, el, gl) }

          // Exact Production for el
          val exact = Seq(el -> Generator(subEls, builder))

          // Inject fix at one place
          val injectG = for ((sgl, i) <- subGls.zipWithIndex) yield {
            gl -> Generator(subEls.updated(i, sgl), builder)
          }

          val swaps = if (subs.size > 1 && !isCommutative(e)) {
            (for (i <- 0 until subs.size;
                 j <- i+1 until subs.size) yield {

              if (subEls(i).getType == subEls(j).getType) {
                val swapSubs = subEls.updated(i, subEls(j)).updated(j, subEls(i))
                Some(gl -> Generator(swapSubs, builder))
              } else {
                None
              }
            }).flatten
          } else {
            Nil
          }

          allSubs ++ exact ++ injectG ++ swaps
        }

        def cegis(gl: L): Seq[(L, Gen)] = {
          normalGrammar.getProductions(gl).map(gl -> _)
        }

        def intVariations(gl: L, v: Int): Seq[(L, Gen)] = {
          Seq(
            gl -> Generator(Nil, { _ => IntLiteral(v-1)} ),
            gl -> Generator(Nil, { _ => IntLiteral(v+1)} )
          )
        }

        val subs: Seq[(L, Gen)] = e match {
          case IntLiteral(v) =>
            gens(e, el, gl, Nil, { _ => e }) ++ cegis(gl) ++ intVariations(gl, v)

          case _: Terminal | _: Let | _: LetTuple | _: LetDef | _: MatchExpr =>
            gens(e, el, gl, Nil, { _ => e }) ++ cegis(gl)

          case FunctionInvocation(TypedFunDef(fd, _), _) if excludeFCalls contains fd =>
            // We allow only exact call, and/or cegis extensions
            Seq(el -> Generator[L, Expr](Nil, { _ => e })) ++ cegis(gl)

          case UnaryOperator(sub, builder) =>
            gens(e, el, gl, List(sub), { case Seq(s) => builder(s) })
          case BinaryOperator(sub1, sub2, builder) =>
            gens(e, el, gl, List(sub1, sub2), { case Seq(s1, s2) => builder(s1, s2) })
          case NAryOperator(subs, builder) =>
            gens(e, el, gl, subs, { case ss => builder(ss) })
        }

        val terminalsMatching = terminals.collect {
          case IsTyped(term, tpe) if tpe == gl.getType && term != e =>
            gl -> Generator[L, Expr](Nil, { _ => term })
        }

        subs ++ terminalsMatching
      }

      val (el, gl) = getLabelPair(e.getType)

      val res = rec(e, el, gl)

      for ((t, g) <- res) {
        val subs = g.subTrees.map { t => FreshIdentifier(t.toString).setType(t.getType).toVariable}
        val gen = g.builder(subs)

        println(f"$t%30s ::= "+gen)
      }
      res
    }
  }

  case class FunctionCalls(prog: Program, currentFunction: FunDef, types: Seq[TypeTree], exclude: Set[FunDef]) extends ExpressionGrammar[TypeTree] {
   def computeProductions(t: TypeTree): Seq[Gen] = {

     def getCandidates(fd: FunDef): Seq[TypedFunDef] = {
       // Prevents recursive calls
       val cfd = currentFunction

       val isRecursiveCall = (prog.callGraph.transitiveCallers(cfd) + cfd) contains fd

       val isDet = fd.body.map(isDeterministic).getOrElse(false)

       if (!isRecursiveCall && isDet) {
         val free = fd.tparams.map(_.tp)
         canBeSubtypeOf(fd.returnType, free, t) match {
           case Some(tpsMap) =>
             val tfd = fd.typed(free.map(tp => tpsMap.getOrElse(tp, tp)))

             if (tpsMap.size < free.size) {
               /* Some type params remain free, we want to assign them:
                *
                * List[T] => Int, for instance, will be found when
                * requesting Int, but we need to assign T to viable
                * types. For that we use list of input types as heuristic,
                * and look for instantiations of T such that input <?:
                * List[T].
                */
               types.distinct.flatMap { (atpe: TypeTree) =>
                 var finalFree = free.toSet -- tpsMap.keySet
                 var finalMap = tpsMap

                 for (ptpe <- tfd.params.map(_.tpe).distinct) {
                   canBeSubtypeOf(atpe, finalFree.toSeq, ptpe) match {
                     case Some(ntpsMap) =>
                       finalFree --= ntpsMap.keySet
                       finalMap  ++= ntpsMap
                     case _ =>
                   }
                 }

                 if (finalFree.isEmpty) {
                   List(fd.typed(free.map(tp => finalMap.getOrElse(tp, tp))))
                 } else {
                   Nil
                 }
               }
             } else {
               /* All type parameters that used to be free are assigned
                */
               List(tfd)
             }
           case None =>
             Nil
         }
       } else {
         Nil
       }
     }

     val funcs = functionsAvailable(prog).toSeq.flatMap(getCandidates).filterNot( tfd => exclude contains tfd.fd)

     funcs.map{ tfd =>
       Generator[TypeTree, Expr](tfd.params.map(_.tpe), { sub => FunctionInvocation(tfd, sub) })
     }
   }
  }

  case class EmbeddedGrammar[Ti <% Typed, To <% Typed](g: ExpressionGrammar[Ti], iToo: Ti => To, oToi: To => Ti) extends ExpressionGrammar[To] {
    
    def computeProductions(t: To): Seq[Gen] = g.computeProductions(oToi(t)).map {
      case g : Generator[Ti, Expr] =>
        Generator(g.subTrees.map(iToo), g.builder)
    }
  }

  case class SafeRecCalls(prog: Program, ws: Expr, pc: Expr) extends ExpressionGrammar[TypeTree] {
    def computeProductions(t: TypeTree): Seq[Gen] = {
      val calls = terminatingCalls(prog, t, ws, pc)

      calls.map {
        case (e, free) =>
          val freeSeq = free.toSeq
          Generator[TypeTree, Expr](freeSeq.map(_.getType), { sub =>
            replaceFromIDs(freeSeq.zip(sub).toMap, e)
          })
      }
    }
  }

  def default(prog: Program, inputs: Seq[Expr], currentFunction: FunDef, exclude: Set[FunDef], ws: Expr, pc: Expr): ExpressionGrammar[TypeTree] = {
    BaseGrammar ||
    OneOf(inputs) ||
    FunctionCalls(prog, currentFunction, inputs.map(_.getType), exclude) ||
    SafeRecCalls(prog, ws, pc)
  }

  def default(sctx: SynthesisContext, p: Problem): ExpressionGrammar[TypeTree] = {
    default(sctx.program, p.as.map(_.toVariable), sctx.functionContext, sctx.settings.functionsToIgnore,  p.ws, p.pc)
  }
}
