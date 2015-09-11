/* Copyright 2009-2015 EPFL, Lausanne */

package leon.regression.synthesis

import leon.test._
import leon._
import leon.synthesis._
import leon.synthesis.graph._
import leon.synthesis.utils._
import leon.utils.PreprocessingPhase

class SynthesisSuite extends LeonRegressionSuite {
  private var counter : Int = 0
  private def nextInt() : Int = {
    counter += 1
    counter
  }

  abstract class SynStrat(val ruleName: String)

  case class Decomp(n: String, sub: Seq[SynStrat]) extends SynStrat(n)

  case class Close(n: String) extends SynStrat(n)


  class TestSearch(ctx: LeonContext,
                   ci: ChooseInfo,
                   p: Problem,
                   strat: SynStrat) extends SimpleSearch(ctx, ci, p, CostModels.default, None) {

    def synthesizeFrom(sctx: SynthesisContext, from: Node, strat: SynStrat): Boolean = {
      from match {
        case an: AndNode =>
          an.expand(SearchContext(sctx, ci, an, this))

          if (an.isSolved) {
            true
          } else if (an.isDeadEnd) {
            false
          } else {
            strat match {
              case Decomp(_, sub) =>
                (an.descendants zip sub).forall {
                  case (n, strat) => synthesizeFrom(sctx, n, strat)
                }
              case _ =>
                fail("Got non-conclusive reply without Decomp strat")
                false
            }
          }

        case on: OrNode =>
          on.expand(SearchContext(sctx, ci, on, this))
          val ns = on.descendants.filter {
            case an: AndNode => matchingDesc(an.ri, strat.ruleName)
            case _ => false
          }

          if (ns.isEmpty) {
            fail("Failed to find rule name: "+strat.ruleName)
          } else if (ns.size > 1) {
            fail("Ambiguous rule name: "+strat.ruleName)
          } else {
            synthesizeFrom(sctx, ns.head, strat)
          }
      }
    }

    override def search(sctx: SynthesisContext): Stream[Solution] = {
      if (synthesizeFrom(sctx, g.root, strat)) {
        g.root.generateSolutions()
      } else {
        Stream.empty
      }
    }

    def matchingDesc(app: RuleInstantiation, n: String): Boolean = {
      import java.util.regex.Pattern
      val pattern = Pattern.quote(n).replace("*", "\\E.*\\Q")
      app.asString(ctx).matches(pattern)
    }

  }

  def forProgram(title: String, opts: Seq[LeonOption[Any]] = Nil)(content: String)(strats: PartialFunction[String, SynStrat]) {
      test(f"Synthesizing ${nextInt()}%3d: [$title]") {
        val ctx = testContext.copy(options = opts ++ testContext.options)

        val pipeline = leon.utils.TemporaryInputPhase andThen
                       leon.frontends.scalac.ExtractionPhase andThen
                       new PreprocessingPhase andThen
                       SynthesisProblemExtractionPhase

        val (program, results) = pipeline.run(ctx)((List(content), Nil))

        for ((f,cis) <- results; ci <- cis) {
          info(f"${ci.fd.id.toString}%-20s")

          val sctx = SynthesisContext(ctx,
                                      SynthesisSettings(),
                                      ci.fd,
                                      program)

          val p      = ci.problem

          if (strats.isDefinedAt(f.id.name)) {
            val search = new TestSearch(ctx, ci, p, strats(f.id.name))

            val sols = search.search(sctx)

            sctx.solverFactory.shutdown()

            if(sols.isEmpty) {
              fail("No solution")
            }
          }
        }
      }
  }

  forProgram("Ground Enum", Seq(LeonOption(SharedOptions.optSelectedSolvers)(Set("enum"))))(
    """
import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object Injection {
  sealed abstract class List
  case class Cons(tail: List) extends List
  case class Nil() extends List

  // proved with unrolling=0
  def size(l: List) : BigInt = (l match {
      case Nil() => BigInt(0)
      case Cons(t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  def simple() = choose{out: List => size(out) == BigInt(2) }
}
    """
  ) {
    case "simple" => Close("Ground")
  }

  forProgram("Cegis 1")(
    """
import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object Injection {
  sealed abstract class List
  case class Cons(tail: List) extends List
  case class Nil() extends List

  // proved with unrolling=0
  def size(l: List) : Int = (l match {
      case Nil() => 0
      case Cons(t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  def simple(in: List) = choose{out: List => size(out) == size(in) }
}
    """
  ) {
    case "simple" => Close("CEGIS")
  }

  forProgram("Cegis 2")(
    """
import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object Injection {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  // simulates input/output spec.
  def tail(in: List) = choose {
    (out: List) =>
      (in != Cons(0, Nil())                   || out == Nil()) &&
      (in != Cons(0, Cons(1, Nil()))          || out == Cons(1, Nil())) &&
      (in != Cons(0, Cons(1, Cons(2, Nil()))) || out == Cons(1, Cons(2, Nil())))
  }
}
    """
  ) {
    case "tail" =>
      Decomp("ADT Split on 'in*'", Seq(
        Close("CEGIS"),
        Close("CEGIS")
      ))
  }


  forProgram("Lists")("""
import leon.lang._
import leon.lang.synthesis._

object SortedList {
  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case class Nil() extends List

  def size(l: List) : BigInt = (l match {
      case Nil() => BigInt(0)
      case Cons(_, t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  def content(l: List): Set[BigInt] = l match {
    case Nil() => Set.empty[BigInt]
    case Cons(i, t) => Set(i) ++ content(t)
  }

  def isSorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, Cons(y, ys)) => x <= y && isSorted(Cons(y, ys))
  }

  def concat(in1: List, in2: List) = choose {
    (out : List) =>
      content(out) == content(in1) ++ content(in2)
  }

  def insert(in1: List, v: BigInt) = choose {
    (out : List) =>
      content(out) == content(in1) ++ Set(v)
  }

  def insertSorted(in1: List, v: BigInt) = choose {
    (out : List) =>
      isSorted(in1) && content(out) == content(in1) ++ Set(v) && isSorted(out)
  }
}
    """) {
    case "concat" =>
      Decomp("ADT Split on 'in1'", List(
        Close("CEGIS"),
        Close("CEGIS")
      ))

    case "insert" =>
      Decomp("ADT Split on 'in1'", List(
        Close("CEGIS"),
        Close("CEGIS")
      ))

    case "insertSorted" =>
      Decomp("Assert isSorted(in1)", List(
        Decomp("ADT Split on 'in1'", List(
          Decomp("Ineq. Split on 'head*' and 'v*'", List(
            Close("CEGIS"),
            Decomp("Equivalent Inputs *", List(
              Decomp("Unused *", List(
                Close("CEGIS")
              ))
            )),
            Close("CEGIS")
          )),
          Close("CEGIS")
        ))
      ))
  }

  forProgram("Church")("""
import leon.lang._
import leon.lang.synthesis._

object ChurchNumerals {
  sealed abstract class Num
  case object Z extends Num
  case class  S(pred: Num) extends Num

  def value(n:Num) : Int = {
    n match {
      case Z => 0
      case S(p) => 1 + value(p)
    }
  } ensuring (_ >= 0)

  // def add(x : Num, y : Num) : Num = (x match {
  //   case Z => y
  //   case S(p) => add(p, S(y))
  // }) ensuring (value(_) == value(x) + value(y))

  def add(x: Num, y: Num): Num = {
    choose { (r : Num) =>
      value(r) == value(x) + value(y)
    }
  }
}
    """) {
    case "add" =>
      Decomp("ADT Split on 'y'", List(
        Close("CEGIS"),
        Close("CEGIS")
      ))
  }

  forProgram("Church")("""
import leon.lang._
import leon.lang.synthesis._

object ChurchNumerals {
  sealed abstract class Num
  case object Z extends Num
  case class  S(pred: Num) extends Num

  def value(n:Num) : Int = {
    n match {
      case Z => 0
      case S(p) => 1 + value(p)
    }
  } ensuring (_ >= 0)

  def add(x : Num, y : Num) : Num = (x match {
    case Z => y
    case S(p) => add(p, S(y))
  }) ensuring (value(_) == value(x) + value(y))

  //def distinct(x : Num, y : Num) : Num = (x match {
  //  case Z =>
  //    S(y)

  //  case S(p) =>
  //    y match {
  //      case Z =>
  //        S(x)
  //      case S(p) =>
  //        Z
  //    }
  //}) ensuring (res => res != x  && res != y)

  def distinct(x: Num, y: Num): Num = {
    choose { (r : Num) =>
      r != x && r != y
    }
  }
}
    """) {
    case "distinct" =>
      Close("CEGIS")
  }
}
