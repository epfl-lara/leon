/*package leon
package transformations
import purescala.Common._
import purescala.Definitions._
import purescala.Extractors._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import invariant.structure._
import invariant.util._
import invariant.util.Util._
import leon.purescala.ScalaPrinter
import leon.utils._

object NonRecursiveTimePhase extends InstrumentationPhase {
  val name = "Non Recursive Time Instrumentation Phase"
  val description = "Allows use of `nonRecTime` in the postconditions"

  def getProgramInstrumenter(p: Program) = {
    new ProgramInstrumenter(p) {
      def getInstrumentationType = NonRecTime

      val nonRecTimeFun =
        Library(p).lookup("leon.instrumentation.nonRecTime") collect { case fd: FunDef => fd }
      def instrumentVariable(e: Expr): Boolean = {
        e match {
          case FunctionInvocation(tfd, _) => {
            if (tfd.fd.id.name == nonRecTimeFun.get.id.name) true else false
          }
          case _ => false
        }
      }
      def instrumentType: TypeTree = IntegerType

      def functionsToInstrument(): Set[FunDef] = getRootFuncs()

      override def additionalfunctionsToAdd(): Seq[FunDef] = Seq()

      var sccs: Map[FunDef, Set[FunDef]] = _;

      override def apply(): Program = {
        // Functions required to have been instrumented for time. These are all
        // the callees of functions needed to be instrumented for nonRecTime
        val timeInstrumentedNeeded = {
          getRootFuncs().foldLeft(Set[FunDef]())(
            (accSet, currFun) => accSet ++ cg.callees(currFun))
        }

        // Functions that need to be time instrumented but aren't currently.
        val timeNeedy =
          timeInstrumentedNeeded.filter {timefd => InstUtil.isInstrumented(timefd, Time) }

        // Instrument timeNeedy functions for Time
        class TimeNeedyProgramInstrumenter(p: Program) extends TimeProgramInstrumenter(p) {
          override def functionsToInstrument(): Set[FunDef] = timeNeedy
        }

        val timeInstrumentedProg = (new TimeNeedyProgramInstrumenter(p))()

        // Compute the call graph of this newly (time) instrumented program.
        // This is needed to compute the strongly conected components to identify
        // mutually recursive calls
        val intermedCg = CallGraphUtil.constructCallGraph(timeInstrumentedProg, onlyBody = true)

        // Strongly connected components
        sccs = intermedCg.graph.sccs.flatMap { scc =>
          scc.map(fd => (fd -> scc.toSet))
        }.toMap

        instFuncs = getRootFuncs(timeInstrumentedProg)

        // Make a copy of the functions, instrument them and create a new program
        val newFuncs = createNewFunDefs(timeInstrumentedProg)

        val mappedFuncs = mapProgram(newFuncs)

        val newprog = createNewProg(mappedFuncs, timeInstrumentedProg)

        newprog
      }

      def getExprInstrumenter(fd: FunDef, funMap: Map[FunDef, FunDef]): ExprInstrumenter = {
        println("NonRecGI called")
        new ExprInstrumenter(fd, funMap) {
          def shouldInstrumentContextual(e: Expr) = true

          def instrumentMatchCase(
            me: MatchExpr,
            mc: MatchCase,
            caseExprCost: Expr,
            scrutineeCost: Expr,
            ignoreMatch: Boolean = false): Expr = {
            val costMatch = if (ignoreMatch) InfiniteIntegerLiteral(0) else costOfExpr(me)

            def totalCostOfMatchPatterns(me: MatchExpr, mc: MatchCase): BigInt = {
              val costOfMatchPattern = 1
              costOfMatchPattern * (1 + me.cases.indexOf(mc))
            }

            Plus(costMatch, Plus(
              Plus(InfiniteIntegerLiteral(totalCostOfMatchPatterns(me, mc)),
                caseExprCost),
              scrutineeCost))
          }

          def isMutuallyRecursiveCall(calleeFd: FunDef): Boolean = {
            if (Set[FunDef](fd).flatMap(sccs.apply _).contains(calleeFd)) true
            else false
          }

          def addSubInstsIfNonZero(subInsts: Seq[Expr], init: Expr): Expr = {
            subInsts.foldLeft(init) {
              case (acc, subinst) if subinst != InfiniteIntegerLiteral(0) =>
                if (acc == InfiniteIntegerLiteral(0)) subinst
                else Plus(acc, subinst)
            }
          }

          def instrumentExpr(e: Expr, subInsts: Seq[Expr], ignoreParent: Boolean = false): Expr = {
            val costOfParent = if (ignoreParent) InfiniteIntegerLiteral(0) else costOfExpr(e)
            e match {
              case t: Terminal => costOfParent
              case FunctionInvocation(tfd, args) => {

                def getTimeExpr(resExpr: Expr): Expr = {
                  //here, we are guaranteed that time instrumentation has happened,
                  //hence, 'tfd.fd' should be an InstFunDef
                  val callee = tfd.fd.asInstanceOf[InstFunDef]
                  val resTimeExpr = InstUtil.resultExprForInstVariable(callee, Time).get
                  val replaceMap: Map[Expr, Expr] =
                    Map(getResVar(tfd.fd).get.toVariable -> resExpr)
                  val origTimeExpr = replace(replaceMap, resTimeExpr)

                  // val timeExpr =
                  if (instFuncs.contains(tfd.fd) && !InstUtil.isInstrumented(callee, NonRecTime)) {
                    origTimeExpr match {
                      case TupleSelect(res, 2) =>
                        TupleSelect(TupleSelect(res, 1), 2)
                      case _ =>
                        throw new IllegalStateException("Instrumentated result value should always be a TupleSelect of form (<Expr>._2)")
                    }
                  } else origTimeExpr
                }

                val funInstExpr = subInsts.last
                val remSubInsts = subInsts.slice(0, subInsts.length - 1)

                // Do not take the callee's time into account if the callee is a
                // mutually recursive function (i.e. in the SCC of the caller)
                if (isMutuallyRecursiveCall(tfd.fd)) {
                  addSubInstsIfNonZero(remSubInsts, costOfParent)
                } else {
                  funInstExpr match {
                    case TupleSelect(resExpr, _) => {
                      val timeExpr = getTimeExpr(resExpr)
                      addSubInstsIfNonZero(remSubInsts, Plus(timeExpr, costOfParent))
                    }
                    case resvar: Variable => {
                      val timeExpr = getTimeExpr(resvar)
                      addSubInstsIfNonZero(remSubInsts, Plus(timeExpr, costOfParent))
                    }
                    case _ =>
                      throw new IllegalStateException("Value of an instrumented variable of a function should always be a TupleSelect")
                  }
                }
              }
              case _ =>
                subInsts.foldLeft(costOfParent: Expr)(
                  (acc: Expr, subeTime: Expr) => Plus(subeTime, acc))
            }
          }

          def instrumentIfThenElseExpr(e: IfExpr, condInst: Option[Expr],
            thenInst: Option[Expr], elzeInst: Option[Expr], ignoreIf: Boolean = false): (Expr, Expr) = {
            val costIf = if (ignoreIf) InfiniteIntegerLiteral(0) else costOfExpr(e)
            (Plus(costIf, Plus(condInst.get, thenInst.get)),
              Plus(costIf, Plus(condInst.get, elzeInst.get)))
          }
        }
      }
    }
  }

  def costOf(e: Expr): Int =
    e match {
      case FunctionInvocation(fd, args) => 1
      case t: Terminal => 0
      case _ => 1
    }

  def costOfExpr(e: Expr) = InfiniteIntegerLiteral(costOf(e))
}*/