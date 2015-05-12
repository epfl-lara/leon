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
import invariant.util.CallGraphUtil
import invariant.structure.FunctionUtils._
import scala.collection.mutable.{Map => MutableMap}

/**
 * An instrumentation phase that performs a sequence of instrumentations
 */

object InstrumentationPhase extends TransformationPhase {
  val name = "Instrumentation Phase"
  val description = "Instruments the program for all counters needed"

  def apply(ctx: LeonContext, program: Program): Program = {
    val instprog = new SerialInstrumenter(ctx, program)
    instprog.apply
  }
}

class SerialInstrumenter(ctx: LeonContext, program: Program) {
  val debugInstrumentation = false

  val instToInstrumenter: Map[Instrumentation, Instrumenter] =
    Map(Time -> new TimeInstrumenter(program, this),
      Depth -> new DepthInstrumenter(program, this),
      Rec -> new RecursionCountInstrumenter(program, this),
      Stack -> new StackSpaceInstrumenter(program, this),
      TPR -> new TPRInstrumenter(program, this))

  // a map from functions to the list of instrumentations to be performed for the function
  lazy val funcInsts = {
    var emap = MutableMap[FunDef,List[Instrumentation]]()
    def update(fd: FunDef, inst: Instrumentation) {
      if (emap.contains(fd))
        emap(fd) = (emap(fd) :+ inst).distinct
      else emap.update(fd, List(inst))
    }
    instToInstrumenter.values.foreach{ m =>
      m.functionsToInstrument.foreach({ case (fd, instsToPerform) =>
        instsToPerform.foreach(instToPerform => update(fd, instToPerform)) })
    }
    emap.toMap
  }
  lazy val instFuncs = funcInsts.keySet //should we exclude theory operations ?

  def instrumenters(fd: FunDef) = funcInsts(fd) map instToInstrumenter.apply _
  def instTypes(fd: FunDef) = funcInsts(fd).map(_.getType)
  /**
   * Index of the instrumentation 'inst' in result tuple that would be created.
   * The return value will be >= 2 as the actual result value would be at index 1
   */
  def instIndex(fd: FunDef)(ins: Instrumentation) = funcInsts(fd).indexOf(ins) + 2
  def selectInst(fd: FunDef)(e: Expr, ins: Instrumentation) = TupleSelect(e, instIndex(fd)(ins))

  def apply: Program = {

    //create new functions. Augment the return type of a function iff the postcondition uses
    //the instrumentation variable or if the function is transitively called from such a function
    //note: need not instrument fields
    val funMap = Util.functionsWOFields(program.definedFunctions).foldLeft(Map[FunDef, FunDef]()) {
      case (accMap, fd: FunDef) if fd.isTheoryOperation =>
        accMap + (fd -> fd)
      case (accMap, fd) => {
        if (instFuncs.contains(fd)) {
          val newRetType = TupleType(fd.returnType +: instTypes(fd))
          // let the names of the function encode the kind of instrumentations performed
          val freshId = FreshIdentifier(fd.id.name + "-" + funcInsts(fd).map(_.name).mkString("-"), newRetType)
          val newfd = new FunDef(freshId, fd.tparams, newRetType, fd.params)
          accMap + (fd -> newfd)
        } else {
          //here we need not augment the return types but do need to create a new copy
          val freshId = FreshIdentifier(fd.id.name, fd.returnType)
          val newfd = new FunDef(freshId, fd.tparams, fd.returnType, fd.params)
          accMap + (fd -> newfd)
        }
      }
    }

    def mapExpr(ine: Expr): Expr = {
      simplePostTransform((e: Expr) => e match {
        case FunctionInvocation(tfd, args) if funMap.contains(tfd.fd) =>
          if (instFuncs.contains(tfd.fd))
            TupleSelect(FunctionInvocation(TypedFunDef(funMap(tfd.fd), tfd.tps), args), 1)
          else
            FunctionInvocation(TypedFunDef(funMap(tfd.fd), tfd.tps), args)
        case _ => e
      })(ine)
    }

    def mapBody(body: Expr, from: FunDef, to: FunDef) = {
      val res = if (instFuncs.contains(from)) {
        (new ExprInstrumenter(funMap)(from)(body))
      } else
        mapExpr(body)
      res
    }

    def mapPost(pred: Expr, from: FunDef, to: FunDef) = {
      pred match {
        case Lambda(Seq(ValDef(fromRes, _)), postCond) if (instFuncs.contains(from)) =>
          val toResId = FreshIdentifier(fromRes.name, to.returnType, true)
          val newpost = postMap((e: Expr) => e match {
            case Variable(`fromRes`) =>
              Some(TupleSelect(toResId.toVariable, 1))

            case _ if funcInsts(from).exists(_.isInstVariable(e)) =>
              val inst = funcInsts(from).find(_.isInstVariable(e)).get
              Some(TupleSelect(toResId.toVariable, instIndex(from)(inst)))

            case _ =>
              None
          })(postCond)
          Lambda(Seq(ValDef(toResId)), mapExpr(newpost))
        case _ =>
          mapExpr(pred)
      }
    }

    // Map the bodies and preconditions
    for ((from, to) <- funMap) {
      //copy annotations
      from.flags.foreach(to.addFlag(_))
      to.fullBody = from.fullBody match {
        case Require(pre, body) =>
          //here 'from' does not have a postcondition but 'to' will always have a postcondition
          val toPost =
            Lambda(Seq(ValDef(FreshIdentifier("res", to.returnType))), BooleanLiteral(true))
          val bodyPre =
            Require(mapExpr(pre), mapBody(body, from, to))
          Ensuring(bodyPre, toPost)

        case Ensuring(Require(pre, body), post) =>
          Ensuring(Require(mapExpr(pre), mapBody(body, from, to)),
            mapPost(post, from, to))

        case Ensuring(body, post) =>
          Ensuring(mapBody(body, from, to), mapPost(post, from, to))

        case body =>
          val toPost =
            Lambda(Seq(ValDef(FreshIdentifier("res", to.returnType))), BooleanLiteral(true))
          Ensuring(mapBody(body, from, to), toPost)
      }
    }

    val additionalFuncs = funMap.flatMap{ case (k, _) =>
       if (instFuncs(k))
        instrumenters(k).flatMap(_.additionalfunctionsToAdd)
      else List()
    }.toList.distinct

    val newprog = Util.copyProgram(program, (defs: Seq[Definition]) =>
      defs.map {
        case fd: FunDef if funMap.contains(fd) =>
           funMap(fd)
        case d => d
      } ++ additionalFuncs)
    if (debugInstrumentation)
      println("After Instrumentation: \n" + ScalaPrinter.apply(newprog))

    ProgramSimplifier(newprog)
  }

  class ExprInstrumenter(funMap: Map[FunDef, FunDef])(implicit currFun: FunDef) {
    val retainMatches = true

    val insts = funcInsts(currFun)
    val instrumenters = SerialInstrumenter.this.instrumenters(currFun)
    val instIndex = SerialInstrumenter.this.instIndex(currFun) _
    val selectInst = SerialInstrumenter.this.selectInst(currFun) _
    val instTypes = SerialInstrumenter.this.instTypes(currFun)

    // Should be called only if 'expr' has to be instrumented
    // Returned Expr is always an expr of type tuple (Expr, Int)
    def tupleify(e: Expr, subs: Seq[Expr], recons: Seq[Expr] => Expr)(implicit letIdMap: Map[Identifier, Identifier]): Expr = {
      // When called for:
      // Op(n1,n2,n3)
      // e      = Op(n1,n2,n3)
      // subs   = Seq(n1,n2,n3)
      // recons = { Seq(newn1,newn2,newn3) => Op(newn1, newn2, newn3) }
      //
      // This transformation should return, informally:
      //
      // LetTuple((e1,t1), transform(n1),
      //   LetTuple((e2,t2), transform(n2),
      //    ...
      //      Tuple(recons(e1, e2, ...), t1 + t2 + ... costOfExpr(Op)
      //    ...
      //   )
      // )
      //
      // You will have to handle FunctionInvocation specially here!
      tupleifyRecur(e, subs, recons, List(), Map())
    }

    def tupleifyRecur(e: Expr, subs: Seq[Expr], recons: Seq[Expr] => Expr, subeVals: List[Expr],
      subeInsts: Map[Instrumentation, List[Expr]])(implicit letIdMap: Map[Identifier, Identifier]): Expr = {
      //note: subs.size should be zero if e is a terminal
      if (subs.size == 0) {
        e match {
          case v @ Variable(id) =>
            val valPart = if (letIdMap.contains(id)) {
              TupleSelect(letIdMap(id).toVariable, 1) //this takes care of replacement
            } else v
            val instPart = instrumenters map (_.instrument(v, Seq()))
            Tuple(valPart +: instPart)

          case t: Terminal =>
            val instPart = instrumenters map (_.instrument(t, Seq()))
            val finalRes = Tuple(t +: instPart)
            finalRes

          case f @ FunctionInvocation(tfd, args) if tfd.fd.isRealFunction =>
            val newfd = funMap(tfd.fd)
            val newFunInv = FunctionInvocation(TypedFunDef(newfd, tfd.tps), subeVals)
            //create a variables to store the result of function invocation
            if (instFuncs(tfd.fd)) {
              //this function is also instrumented
              val resvar = Variable(FreshIdentifier("e", newfd.returnType, true))
              val valexpr = TupleSelect(resvar, 1)
              val instexprs = instrumenters.map { m =>
                val calleeInst = if (funcInsts(tfd.fd).contains(m.inst)) {
                  List(SerialInstrumenter.this.selectInst(tfd.fd)(resvar, m.inst))
                } else List()
                //Note we need to ensure that the last element of list is the instval of the finv
                m.instrument(e, subeInsts.getOrElse(m.inst, List()) ++ calleeInst, Some(resvar))
              }
              Let(resvar.id, newFunInv, Tuple(valexpr +: instexprs))
            } else {
              val resvar = Variable(FreshIdentifier("e", tfd.fd.returnType, true))
              val instexprs = instrumenters.map { m =>
                m.instrument(e, subeInsts.getOrElse(m.inst, List()))
              }
              Let(resvar.id, newFunInv, Tuple(resvar +: instexprs))
            }

          // This case will be taken if the function invocation is actually a val (lazy or otherwise) in the class
          case f @ FunctionInvocation(tfd, args) =>
            val resvar = Variable(FreshIdentifier("e", tfd.fd.returnType, true))
            val instPart = instrumenters map (_.instrument(f, Seq()))
            val finalRes = Tuple(f +: instPart)
            finalRes

          case _ =>
            val exprPart = recons(subeVals)
            val instexprs = instrumenters.zipWithIndex.map {
              case (menter, i) => menter.instrument(e, subeInsts.getOrElse(menter.inst, List()))
            }
            Tuple(exprPart +: instexprs)
        }
      } else {
        val currExp = subs.head
        val resvar = Variable(FreshIdentifier("e", TupleType(currExp.getType +: instTypes), true))
        val eval = TupleSelect(resvar, 1)
        val instMap = insts.map { inst =>
          (inst -> (subeInsts.getOrElse(inst, List()) :+ selectInst(resvar, inst)))
        }.toMap
        //process the remaining arguments
        val recRes = tupleifyRecur(e, subs.tail, recons, subeVals :+ eval, instMap)
        //transform the current expression
        val newCurrExpr = transform(currExp)
        Let(resvar.id, newCurrExpr, recRes)
      }
    }

    /**
     * TODO: need to handle new expression trees
     * Match statements without guards are now instrumented directly
     */
    def transform(e: Expr)(implicit letIdMap: Map[Identifier, Identifier]): Expr = e match {
      // Assume that none of the matchcases has a guard. It has already been converted into an if then else
      case me @ MatchExpr(scrutinee, matchCases) =>
        val containsGuard = matchCases.exists(currCase => currCase.optGuard.isDefined)
        if (containsGuard) {
          def rewritePM(me: MatchExpr): Option[Expr] = {
            val MatchExpr(scrut, cases) = me
            val condsAndRhs = for (cse <- cases) yield {
              val map = mapForPattern(scrut, cse.pattern)
              val patCond = conditionForPattern(scrut, cse.pattern, includeBinders = false)
              val realCond = cse.optGuard match {
                case Some(g) => And(patCond, replaceFromIDs(map, g))
                case None => patCond
              }
              val newRhs = replaceFromIDs(map, cse.rhs)
              (realCond, newRhs)
            }
            val bigIte = condsAndRhs.foldRight[Expr](
              Error(me.getType, "Match is non-exhaustive").copiedFrom(me))((p1, ex) => {
                if (p1._1 == BooleanLiteral(true)) {
                  p1._2
                } else {
                  IfExpr(p1._1, p1._2, ex)
                }
              })
            Some(bigIte)
          }
          transform(rewritePM(me).get)
        } else {
          val instScrutinee =
            Variable(FreshIdentifier("scr", TupleType(scrutinee.getType +: instTypes), true))

          def transformMatchCaseList(mCases: Seq[MatchCase]): Seq[MatchCase] = {
            def transformMatchCase(mCase: MatchCase) = {
              val MatchCase(pattern, guard, expr) = mCase
              val newExpr = {
                val exprVal =
                  Variable(FreshIdentifier("expr", TupleType(expr.getType +: instTypes), true))
                val newExpr = transform(expr)
                val instExprs = instrumenters map { m =>
                  m.instrumentMatchCase(me, mCase, selectInst(exprVal, m.inst),
                    selectInst(instScrutinee, m.inst))
                }
                val letBody = Tuple(TupleSelect(exprVal, 1) +: instExprs)
                Let(exprVal.id, newExpr, letBody)
              }
              MatchCase(pattern, guard, newExpr)
            }
            if (mCases.length == 0) Seq[MatchCase]()
            else {
              transformMatchCase(mCases.head) +: transformMatchCaseList(mCases.tail)
            }
          }
          val matchExpr = MatchExpr(TupleSelect(instScrutinee, 1),
            transformMatchCaseList(matchCases))
          Let(instScrutinee.id, transform(scrutinee), matchExpr)
        }

      case Let(i, v, b) => {
        val (ni, nv) = {
          val ir = Variable(FreshIdentifier("ir", TupleType(v.getType +: instTypes), true))
          val transv = transform(v)
          (ir, transv)
        }
        val r = Variable(FreshIdentifier("r", TupleType(b.getType +: instTypes), true))
        val transformedBody = transform(b)(letIdMap + (i -> ni.id))
        val instexprs = instrumenters map { m =>
          m.instrument(e, List(selectInst(ni, m.inst), selectInst(r, m.inst)))
        }
        Let(ni.id, nv,
          Let(r.id, transformedBody, Tuple(TupleSelect(r, 1) +: instexprs)))
      }

      case ife @ IfExpr(cond, th, elze) => {
        val (nifCons, condInsts) = {
          val rescond = Variable(FreshIdentifier("c", TupleType(cond.getType +: instTypes), true))
          val condInstPart = insts.map { inst => (inst -> selectInst(rescond, inst)) }.toMap
          val recons = (e1: Expr, e2: Expr) => {
            Let(rescond.id, transform(cond), IfExpr(TupleSelect(rescond, 1), e1, e2))
          }
          (recons, condInstPart)
        }
        val (nthenCons, thenInsts) = {
          val resthen = Variable(FreshIdentifier("th", TupleType(th.getType +: instTypes), true))
          val thInstPart = insts.map { inst => (inst -> selectInst(resthen, inst)) }.toMap
          val recons = (theninsts: List[Expr]) => {
            Let(resthen.id, transform(th), Tuple(TupleSelect(resthen, 1) +: theninsts))
          }
          (recons, thInstPart)
        }
        val (nelseCons, elseInsts) = {
          val reselse = Variable(FreshIdentifier("el", TupleType(elze.getType +: instTypes), true))
          val elInstPart = insts.map { inst => (inst -> selectInst(reselse, inst)) }.toMap
          val recons = (einsts: List[Expr]) => {
            Let(reselse.id, transform(elze), Tuple(TupleSelect(reselse, 1) +: einsts))
          }
          (recons, elInstPart)
        }
        val (finalThInsts, finalElInsts) = instrumenters.foldLeft((List[Expr](), List[Expr]())) {
          case ((thinsts, elinsts), menter) =>
            val inst = menter.inst
            val (thinst, elinst) = menter.instrumentIfThenElseExpr(ife,
              Some(condInsts(inst)), Some(thenInsts(inst)), Some(elseInsts(inst)))
            (thinsts :+ thinst, elinsts :+ elinst)
        }
        val nthen = nthenCons(finalThInsts)
        val nelse = nelseCons(finalElInsts)
        nifCons(nthen, nelse)
      }

      // For all other operations, we go through a common tupleifier.
      case n @ Operator(ss, recons) =>
        tupleify(e, ss, recons)

/*      case b @ BinaryOperator(s1, s2, recons) =>
        tupleify(e, Seq(s1, s2), { case Seq(s1, s2) => recons(s1, s2) })

      case u @ UnaryOperator(s, recons) =>
        tupleify(e, Seq(s), { case Seq(s) => recons(s) })
*/
      case t: Terminal =>
        tupleify(e, Seq(), { case Seq() => t })
    }

    def apply(e: Expr): Expr = {
      // Apply transformations
      val newe =
        if (retainMatches) e
        else matchToIfThenElse(liftExprInMatch(e))
      val transformed = transform(newe)(Map())
      val bodyId = FreshIdentifier("bd", transformed.getType, true)
      val instExprs = instrumenters map { m =>
        m.instrumentBody(newe,
          selectInst(bodyId.toVariable, m.inst))

      }
      Let(bodyId, transformed,
        Tuple(TupleSelect(bodyId.toVariable, 1) +: instExprs))
    }

    def liftExprInMatch(ine: Expr): Expr = {
      def helper(e: Expr): Expr = {
        e match {
          case MatchExpr(strut, cases) => strut match {
            case t: Terminal => e
            case _ => {
              val freshid = FreshIdentifier("m", strut.getType, true)
              Let(freshid, strut, MatchExpr(freshid.toVariable, cases))
            }
          }
          case _ => e
        }
      }

      if (retainMatches) helper(ine)
      else simplePostTransform(helper)(ine)
    }
  }
}

/**
 * Implements procedures for a specific instrumentation
 */
abstract class Instrumenter(program: Program, si: SerialInstrumenter) {

  def inst: Instrumentation

  protected val cg = CallGraphUtil.constructCallGraph(program, onlyBody = true)

  def functionsToInstrument(): Map[FunDef, List[Instrumentation]]

  def additionalfunctionsToAdd(): Seq[FunDef]

  def instrumentBody(bodyExpr: Expr, instExpr: Expr)(implicit fd: FunDef): Expr = instExpr

  def getRootFuncs(prog: Program = program): Set[FunDef] = {
    prog.definedFunctions.filter { fd =>
      (fd.hasPostcondition && exists(inst.isInstVariable)(fd.postcondition.get))
    }.toSet
  }

  /**
   * Given an expression to be instrumented
   * and the instrumentation of each of its subexpressions,
   * computes an instrumentation for the procedure.
   * The sub-expressions correspond to expressions returned
   * by Expression Extractors.
   * fd is the function containing the expression `e`
   */
  def instrument(e: Expr, subInsts: Seq[Expr], funInvResVar: Option[Variable] = None)
    (implicit fd: FunDef, letIdMap: Map[Identifier, Identifier]): Expr

  /**
   * Instrument procedure specialized for if-then-else
   */
  def instrumentIfThenElseExpr(e: IfExpr, condInst: Option[Expr],
    thenInst: Option[Expr], elzeInst: Option[Expr]): (Expr, Expr)

  /**
   * This function is expected to combine the cost of the scrutinee,
   * the pattern matching and the expression.
   * The cost model for pattern matching is left to the user.
   * As matches with guards are converted to ifThenElse statements,
   * the user may want to make sure that the cost model for pattern
   * matching across match statements and ifThenElse statements is consistent
   */
  def instrumentMatchCase(me: MatchExpr, mc: MatchCase,
    caseExprCost: Expr, scrutineeCost: Expr): Expr
}