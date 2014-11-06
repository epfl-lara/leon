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

import scala.collection.mutable.{HashMap => MutableMap}

abstract class ExpressionGrammar {
  type Gen = Generator[TypeTree, Expr]

  private[this] val cache = new MutableMap[TypeTree, Seq[Gen]]()

  def getProductions(t: TypeTree): Seq[Gen] = {
    cache.getOrElse(t, {
      val res = computeProductions(t)
      cache += t -> res
      res
    })
  }

  def computeProductions(t: TypeTree): Seq[Gen]

  final def ||(that: ExpressionGrammar): ExpressionGrammar = {
    ExpressionGrammars.Or(Seq(this, that))
  }

  final def printProductions(printer: String => Unit) {
    for ((t, gs) <- cache; g <- gs) {
      val subs = g.subTrees.map { tpe => FreshIdentifier(tpe.toString).setType(tpe).toVariable }
      val gen = g.builder(subs)

      printer(f"$t%30s ::= "+gen)
    }
  }
}

object ExpressionGrammars {

  case class Or(gs: Seq[ExpressionGrammar]) extends ExpressionGrammar {
    val subGrammars: Seq[ExpressionGrammar] = gs.flatMap {
      case o: Or => o.subGrammars
      case g => Seq(g)
    }

    def computeProductions(t: TypeTree): Seq[Gen] =
      subGrammars.flatMap(_.getProductions(t))
  }

  case object Empty extends ExpressionGrammar {
    def computeProductions(t: TypeTree): Seq[Gen] = Nil
  }

  case object BaseGrammar extends ExpressionGrammar {
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

  case class OneOf(inputs: Seq[Expr]) extends ExpressionGrammar {
    def computeProductions(t: TypeTree): Seq[Gen] = {
      inputs.collect {
        case i if isSubtypeOf(i.getType, t) => Generator[TypeTree, Expr](Nil, { _ => i })
      }
    }
  }

  case class SimilarTo(e: Expr, exclude: Set[Expr] = Set()) extends ExpressionGrammar {
    lazy val allSimilar = computeSimilar(e).groupBy(_._1).mapValues(_.map(_._2))

    def computeProductions(t: TypeTree): Seq[Gen] = {
      allSimilar.getOrElse(t, Nil)
    }

    def computeSimilar(e : Expr) : Seq[(TypeTree, Gen)] = {

      var seenSoFar = exclude;

      def gen(retType : TypeTree, tps : Seq[TypeTree], f : Seq[Expr] => Expr) : (TypeTree, Gen) =
        (bestRealType(retType), Generator[TypeTree, Expr](tps.map(bestRealType), f))

      // A generator that always regenerates its input
      def const(e: Expr) = ( bestRealType(e.getType), Generator[TypeTree, Expr](Seq(), _ => e) )

      def rec(e : Expr) : Seq[(TypeTree, Gen)] = {
        if (seenSoFar contains e) {
          Seq()
        } else {
          seenSoFar += e
          val tp = e.getType
          val self: Seq[(TypeTree, Gen)] = e match {
            case RepairHole(_, _) => Seq()
            case _                => Seq(const(e))
          }
          val subs: Seq[(TypeTree, Gen)] = e match {
            case _: Terminal | _: Let | _: LetTuple | _: LetDef | _: MatchExpr =>
              Seq()
            case UnaryOperator(sub, builder) => Seq(
              gen(tp, List(sub.getType), { case Seq(ex) => builder(ex) } )
            ) ++ rec(sub)
            case BinaryOperator(sub1, sub2, builder) => Seq(
              gen(tp, List(sub1.getType, sub2.getType), { case Seq(e1, e2) => builder(e1, e2) } )
            ) ++ rec(sub1) ++ rec(sub2)
            case NAryOperator(subs, builder) => 
              Seq(gen(tp, subs.map(_.getType), builder)) ++ subs.flatMap(rec)
          }

          self ++ subs
        }
      }

      rec(e).tail // Don't want the expression itself
    }
  }

  case class FunctionCalls(prog: Program, currentFunction: FunDef, types: Seq[TypeTree]) extends ExpressionGrammar {
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

     val funcs = functionsAvailable(prog).toSeq.flatMap(getCandidates)

     funcs.map{ tfd =>
       Generator[TypeTree, Expr](tfd.params.map(_.tpe), { sub => FunctionInvocation(tfd, sub) })
     }
   }
  }

  case class SafeRecCalls(prog: Program, pc: Expr) extends ExpressionGrammar {
    def computeProductions(t: TypeTree): Seq[Gen] = {
      val calls = terminatingCalls(prog, t, pc)

      calls.map {
        case (e, free) =>
          val freeSeq = free.toSeq
          Generator[TypeTree, Expr](freeSeq.map(_.getType), { sub =>
            replaceFromIDs(freeSeq.zip(sub).toMap, e)
          })
      }
    }
  }

  def default(prog: Program, inputs: Seq[Expr], currentFunction: FunDef, pc: Expr): ExpressionGrammar = {
    BaseGrammar ||
    OneOf(inputs) ||
    FunctionCalls(prog, currentFunction, inputs.map(_.getType)) ||
    SafeRecCalls(prog, pc)
  }

  def default(sctx: SynthesisContext, p: Problem): ExpressionGrammar = {
    default(sctx.program, p.as.map(_.toVariable), sctx.functionContext, p.pc)
  }
}
