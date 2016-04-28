/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis

import purescala.Definitions._
import purescala.Expressions._
import purescala.Constructors._
import purescala.Common._
import repair._
import leon.utils.ASCIIHelpers._

/** Sets of valid and invalid examples */
case class ExamplesBank(valids: Seq[Example], invalids: Seq[Example]) {
  def examples = valids ++ invalids

  // Minimize tests of a function so that tests that are invalid because of a
  // recursive call are eliminated
  def minimizeInvalids(fd: FunDef, ctx: LeonContext, program: Program): ExamplesBank = {
    val evaluator = new RepairTrackingEvaluator(ctx, program)

    invalids foreach { ts =>
      evaluator.eval(functionInvocation(fd, ts.ins))
    }

    val outInfo = invalids.collect {
      case InOutExample(ins, outs) => ins -> outs
    }.toMap

    val callGraph = evaluator.fullCallGraph

    def isFailing(fi: (FunDef, Seq[Expr])) = !evaluator.fiStatus(fi) && (fi._1 == fd)

    val failing = callGraph filter { case (from, to) =>
      isFailing(from) && (to forall (!isFailing(_)) )
    }

    val newInvalids = failing.keySet map {
      case (_, args) =>
        outInfo.get(args) match {
          case Some(outs) =>
            InOutExample(args, outs)

          case None =>
            InExample(args)
        }
    }

    ExamplesBank(valids, newInvalids.toSeq)
  }

  def union(that: ExamplesBank) = {
    ExamplesBank(
      distinctIns(this.valids union that.valids),
      distinctIns(this.invalids union that.invalids)
    )
  }

  private def distinctIns(s: Seq[Example]): Seq[Example] = {
    val insOuts = s.collect {
      case InOutExample(ins, outs) => ins -> outs
    }.toMap

    s.map(_.ins).distinct.map {
      case ins =>
        insOuts.get(ins) match {
          case Some(outs) => InOutExample(ins, outs)
          case _ => InExample(ins)
        }
    }
  }

  def map(f: Example => List[Example]) = {
    ExamplesBank(valids.flatMap(f), invalids.flatMap(f))
  }

  /** Expands each input example through the function f */
  def mapIns(f: Seq[Expr] => List[Seq[Expr]]) = {
    map {
      case InExample(in) =>
        f(in).map(InExample)

      case InOutExample(in, out) =>
        f(in).map(InOutExample(_, out))
    }
  }

   /** Expands each output example through the function f */
  def mapOuts(f: Seq[Expr] => List[Seq[Expr]]) = {
    map {
      case InOutExample(in, out) =>
        f(out).map(InOutExample(in, _))

      case e =>
        List(e)
    }
  }

  def stripOuts = {
    map {
      case InOutExample(in, out) =>
        List(InExample(in))
      case e =>
        List(e)
    }
  }

  def asString(title: String)(implicit ctx: LeonContext): String = {
    var tt = new Table(title)

    if (examples.nonEmpty) {

      val ow = examples.map {
        case InOutExample(_, out) => out.size
        case _ => 1
      }.max

      val iw = examples.map(_.ins.size).max

      def testsRows(section: String, ts: Seq[Example]) {
        if (tt.rows.nonEmpty) {
          tt += Row(Seq(
            Cell(" ", iw + ow + 1)
          ))
        }

        tt += Row(Seq(
          Cell(Console.BOLD+section+Console.RESET+":", iw + ow + 1)
        ))
        tt += Separator

        for (t <- ts) {
          val os = t match {
            case InOutExample(_, outs) =>
              outs.map(o => Cell(o.asString))
            case _ =>
              Seq(Cell("?", ow))
          }

          tt += Row(
            t.ins.map(i => Cell(i.asString)) ++ Seq(Cell("->")) ++ os
          )
        }
      }

      if (valids.nonEmpty) {
        testsRows("Valid tests", valids)
      }

      if (invalids.nonEmpty) {
        testsRows("Invalid tests", invalids)
      }

      tt.render
    } else {
      "No tests."
    }
  }
}

object ExamplesBank {
  def empty = ExamplesBank(Nil, Nil)

}

/** Same as an ExamplesBank, but with identifiers corresponding to values. This
  * allows us to evaluate expressions. */
case class QualifiedExamplesBank(as: List[Identifier], xs: List[Identifier], eb: ExamplesBank)(implicit hctx: SearchContext) {

  def removeOuts(toRemove: Set[Identifier]): QualifiedExamplesBank = {
    val nxs    = xs.filterNot(toRemove)
    val toKeep = xs.zipWithIndex.filterNot(x => toRemove(x._1)).map(_._2)

    QualifiedExamplesBank(as, nxs, eb mapOuts { out => List(toKeep.map(out)) })
  }

  def removeIns(toRemove: Set[Identifier]) = {
    val nas = as.filterNot(toRemove)
    val toKeep: List[Int] = as.zipWithIndex.filterNot(a => toRemove(a._1)).map(_._2)

    QualifiedExamplesBank(nas, xs, eb mapIns { (in: Seq[Expr]) => List(toKeep.map(in)) })
  }

  /** Filter inputs through expr which is an expression evaluating to a boolean */
  def filterIns(expr: Expr): QualifiedExamplesBank = {
    filterIns(m =>
      hctx.defaultEvaluator.eval(expr, m)
      .result == Some(BooleanLiteral(true)))
  }

  /** Filters inputs through the predicate pred, with an assignment of input variables to expressions. */
  def filterIns(pred: Map[Identifier, Expr] => Boolean): QualifiedExamplesBank = {
    QualifiedExamplesBank(as, xs,
      eb mapIns { in =>
        val m = (as zip in).toMap
        if(pred(m)) {
          List(in)
        } else {
          Nil
        }
      }
    )
  }

  /** Maps inputs through the function f
    * @return A new ExampleBank */
  def mapIns(f: Seq[(Identifier, Expr)] => List[Seq[Expr]]) = {
    eb map {
      case InExample(in) =>
        f(as zip in).map(InExample)

      case InOutExample(in, out) =>
        f(as zip in).map(InOutExample(_, out))
    }
  }
}

import scala.language.implicitConversions

object QualifiedExamplesBank {
  implicit def qebToEb(qeb: QualifiedExamplesBank): ExamplesBank = qeb.eb
}
