package leon
package laziness

import invariant.util._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import LazinessUtil._

class FunctionsManager(p: Program) {

  // includes calls made through the specs
  val cg = CallGraphUtil.constructCallGraph(p, false, true,
    // a specialized callee function that ignores functions called inside `withState` calls, because they would have state as an argument
    (inexpr: Expr) => {
      var callees = Set[FunDef]()
      def rec(e: Expr): Unit = e match {
        case cc @ CaseClass(_, args) if isWithStateCons(cc)(p) =>
          ; //nothing to be done
        case f : FunctionInvocation if isSuspInvocation(f)(p) =>
          // we can ignore the arguments to susp invocation as they are not actual calls, but only a test
          ;
        case cc : CaseClass if isMemCons(cc)(p) =>
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

  /*
   * Lambdas need not be a part of read roots, because its body needs state, the function creating lambda will be
   * marked as needing state.
   */
  val (funsNeedStates, funsRetStates, funsNeedStateTps) = {
    var starRoots = Set[FunDef]()
    var readRoots = Set[FunDef]()
    var valRoots = Set[FunDef]()
    p.definedFunctions.foreach {
      case fd if fd.hasBody =>
        def rec(e: Expr): Unit = e match {
          case finv@FunctionInvocation(_, Seq(CaseClass(_, Seq(Application(l, args))))) if isStarInvocation(finv)(p) =>
            starRoots += fd
            (l +: args) foreach rec
          case finv@FunctionInvocation(_, args) if isCachedInv(finv)(p) =>
            readRoots += fd
            args foreach rec
          case Application(l, args) =>
            valRoots += fd
            (l +: args) foreach rec
          case Operator(args, _) =>
            args foreach rec
        }
        rec(fd.body.get)
      case _ => ;
    }
    val valCallers = cg.transitiveCallers(valRoots.toSeq)
    val readfuns = cg.transitiveCallers(readRoots.toSeq)
    val starCallers = cg.transitiveCallers(starRoots.toSeq)
    //println("Ret roots: "+retRoots.map(_.id)+" ret funs: "+retfuns.map(_.id))
    (readfuns ++ valCallers, valCallers, starCallers ++ readfuns ++ valCallers)
  }

  lazy val callersnTargetOfLambdas = {
    var consRoots = Set[FunDef]()
    //var targets = Set[F]()
    funsNeedStates.foreach {
      case fd if fd.hasBody =>
        postTraversal {
          case l: Lambda =>
            consRoots += fd
            //targets += l
          case _ =>
        }(fd.body.get)
      case _ => ;
    }
    cg.transitiveCallers(consRoots.toSeq) //++ targets
  }

  lazy val cgWithoutSpecs = CallGraphUtil.constructCallGraph(p, true, false)
  lazy val callersOfIsEvalandIsSusp = {
    var roots = Set[FunDef]()
    funsNeedStates.foreach {
      case fd if fd.hasBody =>
        postTraversal {
          case finv: FunctionInvocation if isSuspInvocation(finv)(p) || isCachedInv(finv)(p) =>
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
}
