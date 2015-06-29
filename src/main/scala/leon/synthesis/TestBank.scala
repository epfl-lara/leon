package leon
package synthesis

import purescala.Definitions._
import purescala.Expressions._
import purescala.Constructors._
import evaluators._
import purescala.Common._
import repair._
import leon.utils.ASCIIHelpers._

case class TestBank(valids: Seq[Example], invalids: Seq[Example]) {
  def examples: Seq[Example] = valids ++ invalids

  // Minimize tests of a function so that tests that are invalid because of a
  // recursive call are eliminated
  def minimizeInvalids(fd: FunDef, ctx: LeonContext, program: Program): TestBank = {
    val evaluator = new RepairTrackingEvaluator(ctx, program)

    invalids foreach { ts =>
      evaluator.eval(functionInvocation(fd, ts.ins))
    }

    val outInfo = (invalids.collect {
      case InOutExample(ins, outs) => ins -> outs
    }).toMap

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

    TestBank(valids, newInvalids.toSeq)
  }

  def union(that: TestBank) = {
    TestBank(
      (this.valids ++ that.valids).distinct,
      (this.invalids ++ that.invalids).distinct
    )
  }

  def map(f: Example => List[Example]) = {
    TestBank(valids.flatMap(f), invalids.flatMap(f))
  }

  def mapIns(f: Seq[Expr] => List[Seq[Expr]]) = {
    map {
      case InExample(in) =>
        f(in).map(InExample(_))

      case InOutExample(in, out) =>
        f(in).map(InOutExample(_, out))
    }
  }

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

  def asString(title: String): String = {
    var tt = new Table(title)

    if (examples.nonEmpty) {

      val ow = examples.map {
        case InOutExample(_, out) => out.size
        case _ => 0
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
              outs.map(Cell(_))
            case _ =>
              Seq(Cell("?", ow))
          }

          tt += Row(
            t.ins.map(Cell(_)) ++ Seq(Cell("->")) ++ os
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

object TestBank {
  def empty = TestBank(Nil, Nil)
}

case class ProblemTestBank(p: Problem, tb: TestBank)(implicit hctx: SearchContext) {

  def removeOuts(toRemove: Set[Identifier]) = {
    val toKeep = p.xs.zipWithIndex.filterNot(x => toRemove(x._1)).map(_._2)

    tb mapOuts { out => List(toKeep.map(out)) }
  }

  def removeIns(toRemove: Set[Identifier]) = {
    val toKeep = p.as.zipWithIndex.filterNot(a => toRemove(a._1)).map(_._2)
    tb mapIns { in => List(toKeep.map(in)) }
  }

  def filterIns(expr: Expr) = {
    val ev = new DefaultEvaluator(hctx.sctx.context, hctx.sctx.program)

    tb mapIns { in =>
      val m = (p.as zip in).toMap

      ev.eval(expr, m) match {
        case EvaluationResults.Successful(BooleanLiteral(true)) =>
          List(in)
        case _ =>
          Nil
      }
    }
  }

}
