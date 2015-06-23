package leon
package transformations
import purescala.Common._
import purescala.Definitions._
import purescala.Extractors._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import leon.purescala.ScalaPrinter
import leon.utils._
import invariant.util._

class StackSpaceInstrumenter(p: Program, si: SerialInstrumenter) extends Instrumenter(p, si) {
  val typedMaxFun = TypedFunDef(InstUtil.maxFun, Seq())

  def inst = Stack

  def functionsToInstrument(): Set[FunDef] = {
    // find all functions transitively called from rootFuncs (here ignore functions called via pre/post conditions)
    getRootFuncs().foldLeft(Set[FunDef]())((acc, fd) => acc ++ cg.transitiveCallees(fd))
  }

  def additionalfunctionsToAdd(): Seq[FunDef] = Seq() //Seq(InstUtil.maxFun) - max functions are inlined, so they need not be added

  // Only instrument expressions involving function calls
  /*def shouldInstrumentContextual(e: Expr): Boolean = {
    exists((e: Expr) => {
        e match {
          case FunctionInvocation(_,_) => true
          case _ => false
        }
      }
    )(e)
  }*/

  def addSubInstsIfNonZero(subInsts: Seq[Expr], init: Expr): Expr = {
    subInsts.foldLeft(init)((acc: Expr, subeTime: Expr) => {
      (subeTime, acc) match {
        case (InfiniteIntegerLiteral(x), _) if (x == 0) => acc
        case (_, InfiniteIntegerLiteral(x)) if (x == 0) => subeTime
        case _ => FunctionInvocation(typedMaxFun, Seq(acc, subeTime))
      }
    })
  }

  // Check if a given function call is a tail recursive call
  def isTailCall(call: FunctionInvocation, fd: FunDef): Boolean = {
    if (fd.body.isDefined) {
      def helper(e: Expr): Boolean = {
        e match {
          case FunctionInvocation(_,_) if (e == call) => true
          case Let(binder, value, body) => helper(body)
          case LetDef(_,body) => helper(body)
          case IfExpr(_,thenExpr, elseExpr) => helper(thenExpr) || helper(elseExpr)
          case MatchExpr(_, mCases) => {
            mCases.exists(currCase => helper(currCase.rhs))
          }
          case _ => false
        }
      }
      helper(fd.body.get)
    }
    else false
  }

  def instrumentMatchCase(me: MatchExpr, mc: MatchCase,
    caseExprCost: Expr, scrutineeCost: Expr): Expr = {

    def costOfMatchPattern(me: MatchExpr, mc: MatchCase): Expr = {
      val costOfMatchPattern = 1
      InfiniteIntegerLiteral(costOfMatchPattern)
    }

    addSubInstsIfNonZero(Seq(costOfMatchPattern(me, mc), caseExprCost, scrutineeCost), InfiniteIntegerLiteral(0))
  }

  def instrument(e: Expr, subInsts: Seq[Expr])
    (implicit fd: FunDef, letIdMap: Map[Identifier,Identifier]): Expr = {

    val minActivationRecSize = 5
    e match {
      case t: Terminal => InfiniteIntegerLiteral(0)
      case FunctionInvocation(callFd, args) => {
        // Need to extimate the size of the activation frame of this function.
        //  #Args +
        //  #LocalVals +
        //  #Temporaries created (assume tree-like evaluation of expressions. This will the maximum
        //                        number of temporaries allocated. Also because we assume all the
        //                        temporaries are allocated on the stack and not used only from registers)

        val numTemps =
          if (callFd.body.isDefined) {
            val (temp, stack) = estimateTemporaries(callFd.body.get)
            temp + stack
          } else 0
        val retVar = subInsts.last
        val remSubInsts = subInsts.slice(0, subInsts.length - 1)
        val totalInvocationCost = {
          // model scala's tail recursion optimization here
          if ((isTailCall(FunctionInvocation(callFd, args), fd) && fd.id == callFd.id))
            retVar
          else
            Plus(retVar,
              InfiniteIntegerLiteral(args.length + numTemps + minActivationRecSize))
        }
        val subeTimesExpr = addSubInstsIfNonZero(remSubInsts, InfiniteIntegerLiteral(0))

        subeTimesExpr match {
          case InfiniteIntegerLiteral(x) if (x == 0) => totalInvocationCost
          case _ =>
            addSubInstsIfNonZero(remSubInsts :+ totalInvocationCost, InfiniteIntegerLiteral(0))
        }
      }
      case _ => addSubInstsIfNonZero(subInsts, InfiniteIntegerLiteral(0))
    }
  }

  def instrumentIfThenElseExpr(e: IfExpr, condInst: Option[Expr], thenInst: Option[Expr],
    elzeInst: Option[Expr]): (Expr, Expr) = {
    import invariant.util.Util._
    def optionToList(opte: Option[Expr]) = opte match {
      case Some(x) => List(x)
      case _ => List()
    }
    val cinst = optionToList(condInst)
    val tinst = optionToList(thenInst)
    val einst = optionToList(elzeInst)

    (addSubInstsIfNonZero(cinst ++ tinst, zero),
      addSubInstsIfNonZero(cinst ++ einst, zero))
  }

  /* Tries to estimate the depth of the operand stack and the temporaries
    (excluding arguments) needed by the bytecode. As the JVM might perform
    some optimizations when actually executing the bytecode, what we compute
    here is an upper bound on the memory needed to evaluate the expression
  */
  // (temporaries, stackSize)
  def estimateTemporaries(e: Expr): (Int, Int) = {
    e match {
      /* Like vals */
      case Let(binder: Identifier, value: Expr, body: Expr) => {
      // One for the val created + Temps in expr on RHS of initilisation + Rem. body
        val (valTemp, valStack) = estimateTemporaries(value)
        val (bodyTemp, bodyStack) = estimateTemporaries(body)
        (1 + valTemp + bodyTemp, Math.max(valStack, bodyStack))
      }

      case LetDef(fd: FunDef, body: Expr) => {
      // The function definition does not take up stack space. Goes into the constant pool
        estimateTemporaries(body)
      }

      case FunctionInvocation(tfd: TypedFunDef, args: Seq[Expr]) => {
      // One for the object reference. + stack for computing arguments and also the
      // fact that the arguments go into the stack
        val (temp, stack) =
          args.foldLeft(((0, args.length), 0))((t: ((Int, Int),Int), currExpr) => {
            t match {
              case (acc: (Int, Int), currExprNum: Int) =>
                val (seTemp, seStack) = estimateTemporaries(currExpr)
                ((acc._1 + seTemp, Math.max(acc._2, currExprNum + seStack)), 1 + currExprNum)
            }
          })._1

        (temp, stack + 1)
      }

      case MethodInvocation(rec: Expr, cd: ClassDef, tfd: TypedFunDef, args: Seq[Expr]) => {
        val (recTemp, recStack) = estimateTemporaries(rec)
        val (temp, stack) =
          args.foldLeft(((recTemp, Math.max(args.length, recStack)), 0))((t: ((Int, Int),Int), currExpr) => {
            t match {
              case (acc: (Int, Int), currExprNum: Int) =>
                val (seTemp, seStack) = estimateTemporaries(currExpr)
                ((acc._1 + seTemp, Math.max(acc._2, currExprNum + seStack)), 1 + currExprNum)
            }
          })._1

        (temp, stack + 1)
      }

      // FIXME
      case Application(caller: Expr, args: Seq[Expr]) => {
        val (callerTemp, callerStack) = estimateTemporaries(caller)
        args.foldLeft(((callerTemp, Math.max(args.length, callerStack)), 0))((t: ((Int, Int),Int), currExpr) => {
          t match {
            case (acc: (Int, Int), currExprNum: Int) =>
              val (seTemp, seStack) = estimateTemporaries(currExpr)
              ((acc._1 + seTemp, Math.max(acc._2, currExprNum + seStack)), 1 + currExprNum)
          }
        })._1
      }

      case IfExpr(cond: Expr, thenn: Expr, elze: Expr) => {
        val (condTemp, condStack) = estimateTemporaries(cond)
        val (thennTemp, thennStack) = estimateTemporaries(thenn)
        val (elzeTemp, elzeStack) = estimateTemporaries(elze)

        (condTemp + thennTemp + elzeTemp,
          Math.max(condStack, Math.max(thennStack, elzeStack)))
      }

      case Tuple (exprs: Seq[Expr]) => {
        val (temp, stack) =
          exprs.foldLeft(((0, exprs.length), 0))((t: ((Int, Int),Int), currExpr) => {
            t match {
              case (acc: (Int, Int), currExprNum: Int) =>
                val (seTemp, seStack) = estimateTemporaries(currExpr)
                ((acc._1 + seTemp, Math.max(acc._2, currExprNum + seStack)), 1 + currExprNum)
            }
          })._1

        (temp, stack + 2)
      }

      case MatchExpr(scrutinee: Expr, cases: Seq[MatchCase]) => {

        // FIXME
        def estimateTemporariesMatchPattern(pattern: Pattern): (Int, Int) = {
          pattern match {
            case InstanceOfPattern(binder: Option[Identifier], ct: ClassType) => { // c: Class
              (0,1)
            }

            case WildcardPattern(binder: Option[Identifier]) => { // c @ _
              (0,0)
            }

            case CaseClassPattern(binder: Option[Identifier], ct: CaseClassType, subPatterns: Seq[Pattern]) => {
              val (temp, stack) =
                subPatterns.foldLeft((1, 1))((t: (Int, Int), currPattern) => {
                  t match {
                    case acc: (Int, Int) => {
                      val (patTemp, patStack) = estimateTemporariesMatchPattern(currPattern)
                      (acc._1 + patTemp, Math.max(acc._2, patStack))
                    }
                  }
                })

              (temp, stack)
            }

            case TuplePattern(binder: Option[Identifier], subPatterns: Seq[Pattern]) => {
              val (temp, stack) =
                subPatterns.foldLeft((1, 1))((t: (Int, Int), currPattern) => {
                  t match {
                    case acc: (Int, Int) => {
                      val (patTemp, patStack) = estimateTemporariesMatchPattern(currPattern)
                      (acc._1 + patTemp, Math.max(acc._2, patStack))
                    }
                  }
                })

              (temp, stack)
            }

            case LiteralPattern(binder, lit) => {
              (0,0)
            }
          }
        }

        val (scrTemp, scrStack) = estimateTemporaries(scrutinee)

        cases.foldLeft(((scrTemp, scrStack)))((t: (Int, Int), currCase: MatchCase) => {
          t match {
            case acc: (Int, Int) =>
              val (patTemp, patStack) = estimateTemporariesMatchPattern(currCase.pattern)
              val (rhsTemp, rhsStack) = estimateTemporaries(currCase.rhs)
              val (guardTemp, guardStack) =
                if (currCase.optGuard.isDefined) estimateTemporaries(currCase.optGuard.get) else (0,0)

              (patTemp + rhsTemp + guardTemp,
                Math.max(patStack, Math.max(guardStack, rhsStack)))
          }
        })
      }

      case BinaryOperator(s1,s2,_) => {
        val (s1Temp, s1Stack)= estimateTemporaries(s1)
        val (s2Temp, s2Stack)= estimateTemporaries(s2)
        (s1Temp + s2Temp, Math.max(s1Stack, 1 + s2Stack))
      }

      case NAryOperator(exprs, _) => {
        exprs.foldLeft(((0, exprs.length), 0))((t: ((Int, Int),Int), currExpr) => {
          t match {
            case (acc: (Int, Int), currExprNum: Int) =>
              val (seTemp, seStack) = estimateTemporaries(currExpr)
              ((acc._1 + seTemp, Math.max(acc._2, currExprNum + seStack)), 1 + currExprNum)
          }
        })._1
      }

      /* Propositional logic */
      case Implies(lhs: Expr, rhs: Expr) => {
        val (lhsTemp, lhsStack)= estimateTemporaries(lhs)
        val (rhsTemp, rhsStack)= estimateTemporaries(rhs)
        (rhsTemp + lhsTemp, 1 + Math.max(lhsStack, rhsStack))
      }

      case Not(expr: Expr) => estimateTemporaries(expr)

      case Equals(lhs: Expr, rhs: Expr) => {
        val (lhsTemp, lhsStack)= estimateTemporaries(lhs)
        val (rhsTemp, rhsStack)= estimateTemporaries(rhs)
        (rhsTemp + lhsTemp, 1 + Math.max(lhsStack, rhsStack))
      }

      // FIXME: Is this a constructor call?
      case CaseClass(ct: CaseClassType, args: Seq[Expr]) => {
        val (temp, stack) =
          args.foldLeft(((0, args.length), 0))((t: ((Int, Int),Int), currExpr) => {
            t match {
              case (acc: (Int, Int), currExprNum: Int) =>
                val (seTemp, seStack) = estimateTemporaries(currExpr)
                ((acc._1 + seTemp, Math.max(acc._2, currExprNum + seStack)), 1 + currExprNum)
            }
          })._1

        (temp, stack + 2)
      }

      case _: Literal[_] => (0, 1)

      case Variable(id: Identifier) => (1, 0)

      case Lambda(args: Seq[ValDef], body: Expr) => (0, 0)

      // FIXME
      case Forall(args: Seq[ValDef], body: Expr) => (0, 0)

      // FIXME
      case This(ct: ClassType) => (0, 0)

      case NoTree(tpe: TypeTree) => (0, 0)

      case Choose(pred: Expr, impl_ : Option[Expr]) => (0, 0)

      case TupleSelect(tuple: Expr, index: Int) => (0, 1)

      // FIXME
      case Passes(in: Expr, out : Expr, cases : Seq[MatchCase]) => (0, 0)

      case _ => (0, 0)
    }
  }
}