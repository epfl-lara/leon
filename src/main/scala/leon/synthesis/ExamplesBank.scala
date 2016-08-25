/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis

import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps.minimizeGenericValues
import purescala.Constructors._
import purescala.Extractors._
import purescala.Common._
import evaluators.DefaultEvaluator
import leon.utils.ASCIIHelpers._

/** Sets of valid and invalid examples */
case class ExamplesBank(valids: Seq[Example], invalids: Seq[Example]) {
  def examples = valids ++ invalids

  // Minimize tests of a function so that tests that are invalid because of a
  // recursive call are eliminated
  def minimizeInvalids(fd: FunDef, ctx: LeonContext, program: Program): ExamplesBank = {
    import evaluators._

    if (program.callGraph.isRecursive(fd)) {

      def causeChain(e: Option[Throwable]): List[Expr] = e match {
        case Some(e : ContextualEvaluator#RuntimeError) =>
          e.expr.toList ::: causeChain(e.cause)
        case _ =>
          Nil
      }

      val evaluator = new DefaultEvaluator(ctx, program)

      ctx.timers.repair.tests.minimization.eval.start()

      val newInvalids = invalids map { ts =>
        val newIns = evaluator.eval(functionInvocation(fd, ts.ins)) match {
          case EvaluationResults.RuntimeError(_, cause) =>
            (causeChain(cause).collect {
              case FunctionInvocation(TypedFunDef(`fd`, _), args) =>
                args
            }).lastOption
          case _ =>
            None
        }

        val ins = newIns match {
          case Some(ins) =>
            unwrapTuple(minimizeGenericValues(tupleWrap(ins)), ins.size)
          case None =>
            ts.ins
        }

        InExample(ins)
      }

      ctx.timers.repair.tests.minimization.eval.stop()


      ExamplesBank(valids, newInvalids.distinct)
    } else {
      this
    }
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

  def flatMap(f: Example => List[Example]) = {
    ExamplesBank(valids.flatMap(f), invalids.flatMap(f))
  }

  /** Expands each input example through the function f */
  def flatMapIns(f: Seq[Expr] => List[Seq[Expr]]) = {
    flatMap {
      case InExample(in) =>
        f(in).map(InExample)

      case InOutExample(in, out) =>
        f(in).map(InOutExample(_, out))
    }
  }

   /** Expands each output example through the function f */
  def flatMapOuts(f: Seq[Expr] => List[Seq[Expr]]) = {
     flatMap {
      case InOutExample(in, out) =>
        f(out).map(InOutExample(in, _))

      case e =>
        List(e)
    }
  }

  def stripOuts = {
    flatMap {
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

  // TODO: This might be slightly conservative. We might want something closer to a partial evaluator,
  //       to conserve things like (e: A).isInstanceOf[A] even when evaluation of e leads to choose
  private lazy val evaluator = new DefaultEvaluator(hctx, hctx.program).setEvaluationFailOnChoose(true)

  def removeOuts(toRemove: Set[Identifier]): QualifiedExamplesBank = {
    val nxs    = xs.filterNot(toRemove)
    val toKeep = xs.zipWithIndex.filterNot(x => toRemove(x._1)).map(_._2)

    QualifiedExamplesBank(as, nxs, eb flatMapOuts { out => List(toKeep.map(out)) })
  }

  def removeIns(toRemove: Set[Identifier]) = {
    val nas = as.filterNot(toRemove)
    val toKeep: List[Int] = as.zipWithIndex.filterNot(a => toRemove(a._1)).map(_._2)

    QualifiedExamplesBank(nas, xs, eb flatMapIns { (in: Seq[Expr]) => List(toKeep.map(in)) })
  }

  def evalAndDiscardIns: QualifiedExamplesBank = copy( eb = flatMapIns { mapping =>
    val evalAs = evaluator.evalEnv(mapping)
    try {
      List(as map evalAs)
    } catch {
      case _: NoSuchElementException =>
        Nil
    }
  })

  /** Filter inputs through expr which is an expression evaluating to a boolean */
  def filterIns(expr: Expr): QualifiedExamplesBank = {
    filterIns(m => evaluator.eval(expr, m).result.contains(BooleanLiteral(true)))
  }

  /** Filters inputs through the predicate pred, with an assignment of input variables to expressions. */
  def filterIns(pred: Map[Identifier, Expr] => Boolean): QualifiedExamplesBank = {
    QualifiedExamplesBank(as, xs,
      eb flatMapIns { in =>
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
    *
    * @return A new ExampleBank */
  def flatMapIns(f: Seq[(Identifier, Expr)] => List[Seq[Expr]]): ExamplesBank = {
    eb flatMap {
      case InExample(in) =>
        f(as zip in).map(InExample)

      case InOutExample(in, out) =>
        f(as zip in).map(InOutExample(_, out))
    }
  }

  def asConstraint: Expr = {
    andJoin(eb.valids.map {
      case InOutExample(ins, outs) =>
        val in  = andJoin(as.map(_.toVariable).zip(ins) .map { case (a,b) => equality(a,b) })
        val out = andJoin(xs.map(_.toVariable).zip(outs).map { case (a,b) => equality(a,b) })

        implies(in, out)

      case _ =>
        BooleanLiteral(true)
    })
  }
}

import scala.language.implicitConversions

object QualifiedExamplesBank {
  implicit def qebToEb(qeb: QualifiedExamplesBank): ExamplesBank = qeb.eb
}
