/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package utils

import bonsai._

import Helpers._

import purescala.Expressions.{Or => LeonOr, _}
import purescala.Common._
import purescala.Definitions._
import purescala.Types._
import purescala.ExprOps._
import purescala.TypeOps._
import purescala.Extractors._
import purescala.Constructors._
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

  def filter(f: Gen => Boolean) = {
    new ExpressionGrammar[T] {
      def computeProductions(t: T) = ExpressionGrammar.this.computeProductions(t).filter(f)
    }
  }

  final def ||(that: ExpressionGrammar[T]): ExpressionGrammar[T] = {
    ExpressionGrammars.Or(Seq(this, that))
  }
 

  final def printProductions(printer: String => Unit) {
    for ((t, gs) <- cache; g <- gs) {
      val subs = g.subTrees.map { t => FreshIdentifier(Console.BOLD+t.toString+Console.RESET, t.getType).toVariable}
      val gen = g.builder(subs)

      printer(f"${Console.BOLD}$t%30s${Console.RESET} ::= $gen")
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
          Generator(Nil, { _ => BooleanLiteral(false) }),
          Generator(List(BooleanType),              { case Seq(a)    => not(a) }),
          Generator(List(BooleanType, BooleanType), { case Seq(a, b) => and(a, b) }),
          Generator(List(BooleanType, BooleanType), { case Seq(a, b) => or(a, b) }),
          Generator(List(Int32Type, Int32Type),     { case Seq(a, b) => LessThan(a, b) }),
          Generator(List(Int32Type, Int32Type),     { case Seq(a, b) => LessEquals(a, b) }),
          Generator(List(Int32Type,   Int32Type  ), { case Seq(a, b) => equality(a, b) }),
          Generator(List(IntegerType, IntegerType), { case Seq(a, b) => LessThan(a, b) }),
          Generator(List(IntegerType, IntegerType), { case Seq(a, b) => LessEquals(a, b) }),
          Generator(List(IntegerType, IntegerType), { case Seq(a, b) => equality(a, b) }),
          Generator(List(BooleanType, BooleanType), { case Seq(a, b) => equality(a, b) })
        )
      case Int32Type =>
        List(
          Generator(Nil, { _ => IntLiteral(0) }),
          Generator(Nil, { _ => IntLiteral(1) }),
          Generator(List(Int32Type, Int32Type), { case Seq(a,b) => plus(a, b) }),
          Generator(List(Int32Type, Int32Type), { case Seq(a,b) => minus(a, b) }),
          Generator(List(Int32Type, Int32Type), { case Seq(a,b) => times(a, b) })
        )

      case IntegerType =>
        List(
          Generator(Nil, { _ => InfiniteIntegerLiteral(0) }),
          Generator(Nil, { _ => InfiniteIntegerLiteral(1) }),
          Generator(List(IntegerType, IntegerType), { case Seq(a,b) => plus(a, b) }),
          Generator(List(IntegerType, IntegerType), { case Seq(a,b) => minus(a, b) }),
          Generator(List(IntegerType, IntegerType), { case Seq(a,b) => times(a, b) })
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
          Generator(List(base),   { case elems     => finiteSet(elems.toSet, base) }),
          Generator(List(st, st), { case Seq(a, b) => SetUnion(a, b) }),
          Generator(List(st, st), { case Seq(a, b) => SetIntersection(a, b) }),
          Generator(List(st, st), { case Seq(a, b) => SetDifference(a, b) })
        )

      case UnitType =>
        List( Generator(Nil, { case _ => UnitLiteral() }) )

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
          Generator(Nil, { _ => IntLiteral(42) })
        )
      case IntegerType =>
        List(
          Generator(Nil, { _ => InfiniteIntegerLiteral(0) }),
          Generator(Nil, { _ => InfiniteIntegerLiteral(1) }),
          Generator(Nil, { _ => InfiniteIntegerLiteral(42) })
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
          Generator(List(base),       { case elems => finiteSet(elems.toSet, base) }),
          Generator(List(base, base), { case elems => finiteSet(elems.toSet, base) })
        )
      
      case UnitType =>
        List( Generator(Nil, { case _ => UnitLiteral() }) )

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

  case class Label[T](t: TypeTree, l: T, depth: Option[Int] = None) extends Typed {
    def getType = t

    override def toString = t.toString+"#"+l+depth.map(d => "@"+d).getOrElse("")
  }

  case class SimilarTo(e: Expr, terminals: Set[Expr] = Set(), sctx: SynthesisContext, p: Problem) extends ExpressionGrammar[Label[String]] {

    val excludeFCalls = sctx.settings.functionsToIgnore
    
    val normalGrammar = BoundedGrammar(EmbeddedGrammar(
        BaseGrammar ||
        OneOf(terminals.toSeq :+ e) ||
        FunctionCalls(sctx.program, sctx.functionContext, p.as.map(_.getType), excludeFCalls) ||
        SafeRecCalls(sctx.program, p.ws, p.pc),
      { (t: TypeTree)      => Label(t, "B", None)},
      { (l: Label[String]) => l.getType }
    ), 1)
    
    type L = Label[String]

    val getNext: () => Int = {
      var counter = -1
      () => {
        counter += 1
        counter
      }
    }

    lazy val allSimilar = computeSimilar(e).groupBy(_._1).mapValues(_.map(_._2))

    def computeProductions(t: L): Seq[Gen] = {
      t match {
        case Label(_, "B", _) => normalGrammar.computeProductions(t)
        case _                => allSimilar.getOrElse(t, Nil)
      }
    }

    def computeSimilar(e : Expr) : Seq[(L, Gen)] = {

      def getLabel(t: TypeTree) = {
        val tpe = bestRealType(t)
        val c = getNext()
        Label(tpe, "G"+c)
      }

      def isCommutative(e: Expr) = e match {
        case _: Plus | _: Times => true
        case _ => false
      }

      def rec(e: Expr, gl: L): Seq[(L, Gen)] = {

        def gens(e: Expr, gl: L, subs: Seq[Expr], builder: (Seq[Expr] => Expr)): Seq[(L, Gen)] = {
          val subGls = subs.map { s => getLabel(s.getType) }

          // All the subproductions for sub gl
          val allSubs = (subs zip subGls).flatMap { case (e, gl) => rec(e, gl) }

          // Inject fix at one place
          val injectG = for ((sgl, i) <- subGls.zipWithIndex) yield {
            gl -> Generator[L, Expr](Seq(sgl), { case Seq(ge) => builder(subs.updated(i, ge)) } )
          }

          val swaps = if (subs.size > 1 && !isCommutative(e)) {
            (for (i <- 0 until subs.size;
                 j <- i+1 until subs.size) yield {

              if (subs(i).getType == subs(j).getType) {
                val swapSubs = subs.updated(i, subs(j)).updated(j, subs(i))
                Some(gl -> Generator[L, Expr](Seq(), { _ => builder(swapSubs) }))
              } else {
                None
              }
            }).flatten
          } else {
            Nil
          }

          allSubs ++ injectG ++ swaps
        }

        def cegis(gl: L): Seq[(L, Gen)] = {
          normalGrammar.getProductions(gl).map(gl -> _)
        }

        def intVariations(gl: L, e : Expr): Seq[(L, Gen)] = {
          Seq(
            gl -> Generator(Nil, { _ => BVMinus(e, IntLiteral(1))} ),
            gl -> Generator(Nil, { _ => BVPlus (e, IntLiteral(1))} )
          )
        }

        // Find neighbor case classes that are compatible with the arguments:
        // Turns And(e1, e2) into Or(e1, e2)...
        def ccVariations(gl: L, cc: CaseClass): Seq[(L, Gen)] = {
          val CaseClass(cct, args) = cc

          val neighbors = cct.parent.map(_.knownCCDescendents).getOrElse(Seq()).filter(_ != cct)

          for (scct <- neighbors if scct.fieldsTypes == cct.fieldsTypes) yield {
            gl -> Generator[L, Expr](Nil, { _ => CaseClass(scct, args) })
          }
        }

        val funFilter = (fd: FunDef) => fd.isSynthetic || (excludeFCalls contains fd)
        val subs: Seq[(L, Gen)] = (e match {
          
          case _: Terminal | _: Let | _: LetDef | _: MatchExpr =>
            gens(e, gl, Nil, { _ => e }) ++ cegis(gl)

          case cc @ CaseClass(cct, exprs) =>
            gens(e, gl, exprs, { case ss => CaseClass(cct, ss) }) ++ ccVariations(gl, cc)

          case FunctionInvocation(TypedFunDef(fd, _), _) if funFilter(fd) =>
            // We allow only exact call, and/or cegis extensions
            /*Seq(el -> Generator[L, Expr](Nil, { _ => e })) ++*/ cegis(gl)

          case UnaryOperator(sub, builder) =>
            gens(e, gl, List(sub), { case Seq(s) => builder(s) })
          case BinaryOperator(sub1, sub2, builder) =>
            gens(e, gl, List(sub1, sub2), { case Seq(s1, s2) => builder(s1, s2) })

          case NAryOperator(subs, builder) =>
            gens(e, gl, subs, { case ss => builder(ss) })
        }) ++ (if (e.getType == Int32Type ) intVariations(gl, e) else Nil)

        val terminalsMatching = terminals.collect {
          case IsTyped(term, tpe) if tpe == gl.getType && term != e =>
            gl -> Generator[L, Expr](Nil, { _ => term })
        }

        subs ++ terminalsMatching
      }

      val gl = getLabel(e.getType)

      val res = rec(e, gl)

      //for ((t, g) <- res) {
      //  val subs = g.subTrees.map { t => FreshIdentifier(t.toString, t.getType).toVariable}
      //  val gen = g.builder(subs)

      //  println(f"$t%30s ::= "+gen)
      //}
      res
    }
  }

  case class FunctionCalls(prog: Program, currentFunction: FunDef, types: Seq[TypeTree], exclude: Set[FunDef]) extends ExpressionGrammar[TypeTree] {
   def computeProductions(t: TypeTree): Seq[Gen] = {

     def getCandidates(fd: FunDef): Seq[TypedFunDef] = {
       // Prevents recursive calls
       val cfd = currentFunction

       val isRecursiveCall = (prog.callGraph.transitiveCallers(cfd) + cfd) contains fd

       val isDet = fd.body.exists(isDeterministic)

       if (!isRecursiveCall && isDet) {
         val free = fd.tparams.map(_.tp)
         canBeSubtypeOf(fd.returnType, free, t, rhsFixed = true) match {
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

                 for (ptpe <- tfd.params.map(_.getType).distinct) {
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

     val filter = (tfd:TypedFunDef) => tfd.fd.isSynthetic || (exclude contains tfd.fd)
     val funcs = functionsAvailable(prog).toSeq.flatMap(getCandidates).filterNot(filter)

     funcs.map{ tfd =>
       Generator[TypeTree, Expr](tfd.params.map(_.getType), { sub => FunctionInvocation(tfd, sub) })
     }
   }
  }

  case class BoundedGrammar[T](g: ExpressionGrammar[Label[T]], bound: Int) extends ExpressionGrammar[Label[T]] {
    def computeProductions(l: Label[T]): Seq[Gen] = g.computeProductions(l).flatMap {
      case g: Generator[Label[T], Expr] =>
        if (l.depth == Some(bound) && g.subTrees.nonEmpty) {
          None  
        } else if (l.depth.exists(_ > bound)) {
          None
        } else {
          Some(Generator(g.subTrees.map(sl => sl.copy(depth = l.depth.map(_+1).orElse(Some(1)))), g.builder))
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

  def depthBound[T <% Typed](g: ExpressionGrammar[T], b: Int) = {
    g.filter(g => g.subTrees.forall(t => typeDepth(t.getType) <= b))
  }
}
