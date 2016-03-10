package leon
package laziness

import invariant.util._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import LazinessUtil._

class LazyFunctionsManager(p: Program) {

  // includes calls made through the specs
  val cg = CallGraphUtil.constructCallGraph(p, false, true,
    // a specialized callee function that ignores functions called inside `withState` calls, because they would have state as an argument
    (inexpr: Expr) => {
      var callees = Set[FunDef]()
      def rec(e: Expr): Unit = e match {
        case cc @ CaseClass(_, args) if LazinessUtil.isWithStateCons(cc)(p) =>
          ; //nothing to be done
        case f : FunctionInvocation if LazinessUtil.isSuspInvocation(f)(p) =>
          // we can ignore the arguments to susp invocation as they are not actual calls, but only a test
          ;
        case cc : CaseClass if LazinessUtil.isMemCons(cc)(p) =>
          ; // we can ignore the arguments to mem
        //note: do not consider field invocations
        case f @ FunctionInvocation(TypedFunDef(callee, _), args) if callee.isRealFunction =>
          callees += callee
          args map rec
        case Operator(args, _) => args map rec
      }
      rec(inexpr)
      callees
    })

  val (funsNeedStates, funsRetStates, funsNeedStateTps) = {
    var starRoots = Set[FunDef]()
    var readRoots = Set[FunDef]()
    var valRoots = Set[FunDef]()
    p.definedFunctions.foreach {
      case fd if fd.hasBody =>
        postTraversal {
          case finv: FunctionInvocation if isStarInvocation(finv)(p) =>
            starRoots += fd
          case finv: FunctionInvocation if isLazyInvocation(finv)(p) =>
            // the lazy invocation constructor will need the state
            readRoots += fd
          case finv: FunctionInvocation if isEvaluatedInvocation(finv)(p) || isCachedInv(finv)(p) =>
            readRoots += fd
          case finv: FunctionInvocation if isValueInvocation(finv)(p) =>
            valRoots += fd
          case _ =>
            ;
        }(fd.body.get)
      case _ => ;
    }
    val valCallers = cg.transitiveCallers(valRoots.toSeq)
    val readfuns = cg.transitiveCallers(readRoots.toSeq)
    val starCallers = cg.transitiveCallers(starRoots.toSeq)
    //println("Ret roots: "+retRoots.map(_.id)+" ret funs: "+retfuns.map(_.id))
    (readfuns ++ valCallers, valCallers, starCallers ++ readfuns ++ valCallers)
  }

  lazy val callersnTargetOfLazyCons = {
    var consRoots = Set[FunDef]()
    var targets = Set[FunDef]()
    funsNeedStates.foreach {
      case fd if fd.hasBody =>
        postTraversal {
          case finv: FunctionInvocation if isLazyInvocation(finv)(p) => // this is the lazy invocation constructor
            consRoots += fd
            targets += finv.tfd.fd
          case _ =>
            ;
        }(fd.body.get)
      case _ => ;
    }
    cg.transitiveCallers(consRoots.toSeq) ++ targets
  }

  lazy val cgWithoutSpecs = CallGraphUtil.constructCallGraph(p, true, false)
  lazy val callersOfIsEvalandIsSusp = {
    var roots = Set[FunDef]()
    funsNeedStates.foreach {
      case fd if fd.hasBody =>
        postTraversal {
          case finv: FunctionInvocation if
            isEvaluatedInvocation(finv)(p) || isSuspInvocation(finv)(p) || isCachedInv(finv)(p) => // call to isEvaluated || isSusp ?
            roots += fd
          case _ =>
            ;
        }(fd.body.get)
      case _ => ;
    }
    cgWithoutSpecs.transitiveCallers(roots.toSeq)
  }

  def isRecursive(fd: FunDef) : Boolean = {
    cg.isRecursive(fd)
  }

  def hasStateIndependentBehavior(fd: FunDef) : Boolean = {
    // every function that does not call isEvaluated or is Susp has a state independent behavior
    !callersOfIsEvalandIsSusp.contains(fd)
  }

//  lazy val targetsOfLazyCons = {
//    var callees = Set[FunDef]()
//    funsNeedStates.foreach {
//      case fd if fd.hasBody =>
//        postTraversal {
//          case finv: FunctionInvocation if isLazyInvocation(finv)(p) => // this is the lazy invocation constructor
//            callees += finv.tfd.fd
//          case _ =>
//            ;
//        }(fd.body.get)
//      case _ => ;
//    }
//    callees
//  }

}
