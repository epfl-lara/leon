package leon
package purescala

import Definitions._
import Trees._
import TreeOps._

class CallGraph(p: Program) {

  private var _calls = Set[(FunDef, FunDef)]()

  private var _callers = Map[FunDef, Set[FunDef]]() // if 'foo' calls 'bar': Map(bar -> Set(foo))
  private var _callees = Map[FunDef, Set[FunDef]]() // if 'foo' calls 'bar': Map(foo -> Set(bar))

  private var _transitiveCalls   = Set[(FunDef, FunDef)]()
  private var _transitiveCallers = Map[FunDef, Set[FunDef]]()
  private var _transitiveCallees = Map[FunDef, Set[FunDef]]()

  def allCalls = _calls
  def allTransitiveCalls = _transitiveCalls

  def isRecursive(f: FunDef) = transitivelyCalls(f, f)

  def calls(from: FunDef, to: FunDef) = _calls contains (from -> to)
  def callers(to: FunDef)   = _callers.getOrElse(to, Set())
  def callees(from: FunDef) = _callees.getOrElse(from, Set())

  def transitivelyCalls(from: FunDef, to: FunDef) = _transitiveCalls contains (from -> to)
  def transitiveCallers(to: FunDef)   = _transitiveCallers.getOrElse(to, Set())
  def transitiveCallees(from: FunDef) = _transitiveCallees.getOrElse(from, Set())

  // multi-source/dest
  def callees(from: Set[FunDef]): Set[FunDef] = from.flatMap(callees)
  def callers(to: Set[FunDef]): Set[FunDef] = to.flatMap(callers)
  def transitiveCallees(from: Set[FunDef]): Set[FunDef] = from.flatMap(transitiveCallees)
  def transitiveCallers(to: Set[FunDef]): Set[FunDef] = to.flatMap(transitiveCallers)

  private def init() {
    _calls   = Set()
    _callers = Map()
    _callees = Map()


    // Collect all calls
    p.definedFunctions.foreach(scanForCalls)

    _transitiveCalls   = _calls
    _transitiveCallers = _callers
    _transitiveCallees = _callees

    // Transitive calls
    transitiveClosure()
  }

  private def collectCalls(fd: FunDef)(e: Expr): Set[(FunDef, FunDef)] = e match {
    case f @ FunctionInvocation(f2, _) => Set((fd, f2.fd))
    case _ => Set()
  }

  private def scanForCalls(fd: FunDef) {
    val allExprs: Iterable[Expr] = 
      fd.precondition ++ fd.body ++ fd.postcondition.map(_._2)

    for (e <- allExprs; (from, to) <- collect(collectCalls(fd)(_))(e)) {
      _calls   += (from -> to)
      _callees += (from -> (_callees.getOrElse(from, Set()) + to))
      _callers += (to   -> (_callers.getOrElse(to, Set()) + from))
    }
  }

  private def transitiveClosure() {
    var changed = true;
    while(changed) {
      val newCalls = _transitiveCalls.flatMap {
        case (from, to) => _transitiveCallees.getOrElse(to, Set()).map((from, _))
      } -- _transitiveCalls

      if (newCalls.nonEmpty) {
        for ((from, to) <- newCalls) {
          _transitiveCalls   += (from -> to)
          _transitiveCallees += (from -> (_transitiveCallees.getOrElse(from, Set()) + to))
          _transitiveCallers += (to   -> (_transitiveCallers.getOrElse(to, Set()) + from))
        }
      } else {
        changed =false
      }
    }
  }

  init()
}
