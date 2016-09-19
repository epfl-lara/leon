/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import Definitions._
import Expressions._
import ExprOps._
import Extractors._
import laziness.HOMemUtil._

import utils.Graphs._

class CallGraph(p: Program) {

  private def collectCallsInPats(fd: FunDef)(p: Pattern): Set[(FunDef, FunDef)] =
    (p match {
      case u: UnapplyPattern => Set((fd, u.unapplyFun.fd))
      case _ => Set()
    }) ++ p.subPatterns.flatMap(collectCallsInPats(fd))

  /*private def collectCalls(fd: FunDef)(e: Expr): Set[(FunDef, FunDef)] = e match {
    // extensions for handling `memoized` benchmarks
    case f : FunctionInvocation if cachedInvocation(f)(p) || isIsFun(f)(p) => Set()
    case f @ FunctionInvocation(f2, _) => Set((fd, f2.fd))
    case MatchExpr(_, cases) => cases.toSet.flatMap((mc: MatchCase) => collectCallsInPats(fd)(mc.pattern))
    case _ => Set()
  }*/

  // do a pre-order traversal so as handle extensions for handling `memoized` benchmarks
  private def collectCalls(fd: FunDef)(e: Expr): Set[(FunDef, FunDef)] ={
    e match {
      case f: FunctionInvocation if cachedInvocation(f) || isIsFun(f) => Set()
      case f @ FunctionInvocation(f2, args) =>
        (args.flatMap(collectCalls(fd)).toSet) ++ Set((fd, f2.fd))
      case MatchExpr(scr, cases) =>
        collectCalls(fd)(scr) ++
          (cases.toSet.flatMap { (c: MatchCase) =>
            c match {
              case MatchCase(pat, g, rhs) =>
                (collectCallsInPats(fd)(pat) ++ g.map(collectCalls(fd)).getOrElse(Set()) ++ collectCalls(fd)(rhs))
            }
          })
      case Operator(args, _) => args.toSet.flatMap(collectCalls(fd))
    }
  }

  lazy val graph: DiGraph[FunDef, SimpleEdge[FunDef]] = {
    var g = DiGraph[FunDef, SimpleEdge[FunDef]]()

    for (fd <- p.definedFunctions; c <- collectCalls(fd)(fd.fullBody) ++
        fd.decreaseMeasure.toList.flatMap(collectCalls(fd))) {
      g += SimpleEdge(c._1, c._2)
    }

    g
  }

  lazy val allCalls = graph.E.map(e => e._1 -> e._2)

  def isRecursive(f: FunDef) = {
    graph.transitiveSucc(f) contains f
  }

  def calls(from: FunDef, to: FunDef) = {
    graph.E contains SimpleEdge(from, to)
  }

  def callers(to: FunDef): Set[FunDef] = {
    graph.pred(to)
  }

  def callers(tos: Set[FunDef]): Set[FunDef] = {
    tos.flatMap(callers)
  }

  def callees(from: FunDef): Set[FunDef] = {
    graph.succ(from)
  }

  def callees(froms: Set[FunDef]): Set[FunDef] = {
    froms.flatMap(callees)
  }

  def transitiveCallers(to: FunDef): Set[FunDef] = {
    graph.transitivePred(to)
  }

  def transitiveCallers(tos: Set[FunDef]): Set[FunDef] = {
    tos.flatMap(transitiveCallers)
  }

  def transitiveCallees(from: FunDef): Set[FunDef] = {
    graph.transitiveSucc(from)
  }

  def transitiveCallees(froms: Set[FunDef]): Set[FunDef] = {
    froms.flatMap(transitiveCallees)
  }

  def transitivelyCalls(from: FunDef, to: FunDef): Boolean = {
    graph.transitiveSucc(from) contains to
  }

  lazy val stronglyConnectedComponents = graph.stronglyConnectedComponents.N
}
