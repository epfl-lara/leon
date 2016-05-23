/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import Definitions._
import Expressions._
import ExprOps._

import utils.Graphs._

class CallGraph(p: Program) {

  private def collectCallsInPats(fd: FunDef)(p: Pattern): Set[(FunDef, FunDef)] =
    (p match {
      case u: UnapplyPattern => Set((fd, u.unapplyFun.fd))
      case _ => Set()
    }) ++ p.subPatterns.flatMap(collectCallsInPats(fd))

  private def collectCalls(fd: FunDef)(e: Expr): Set[(FunDef, FunDef)] = e match {
    case f @ FunctionInvocation(f2, _) => Set((fd, f2.fd))
    case MatchExpr(_, cases) => cases.toSet.flatMap((mc: MatchCase) => collectCallsInPats(fd)(mc.pattern))
    case _ => Set()
  }

  lazy val graph: DiGraph[FunDef, SimpleEdge[FunDef]] = {
    var g = DiGraph[FunDef, SimpleEdge[FunDef]]()

    for (fd <- p.definedFunctions; c <- collect(collectCalls(fd))(fd.fullBody)) {
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
