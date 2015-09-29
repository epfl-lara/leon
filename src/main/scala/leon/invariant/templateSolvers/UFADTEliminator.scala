package leon
package invariant.templateSolvers
import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import java.io._
import leon.invariant.util.UndirectedGraph
import scala.util.control.Breaks._
import invariant.util._
import leon.purescala.TypeOps

class UFADTEliminator(ctx: LeonContext, program: Program) {

  val debugAliases = false
  val makeEfficient = true //this will happen at the expense of completeness
  val reporter = ctx.reporter
  val verbose = false

  def collectCompatibleCalls(calls: Set[Expr]) = {
    //compute the cartesian product of the calls and select the pairs having the same function symbol and also implied by the precond
    val vec = calls.toArray
    val size = calls.size
    var j = 0
    //for stats
    var tuples = 0
    var functions = 0
    var adts = 0
    val product = vec.foldLeft(Set[(Expr, Expr)]())((acc, call) => {

      //an optimization: here we can exclude calls to maxFun from axiomatization, they will be inlined anyway
      /*val shouldConsider = if(InvariantUtil.isCallExpr(call)) {
        val BinaryOperator(_,FunctionInvocation(calledFun,_), _) = call
        if(calledFun == DepthInstPhase.maxFun) false
        else true
      } else true*/
      var pairs = Set[(Expr, Expr)]()
      for (i <- j + 1 until size) {
        val call2 = vec(i)
        if (mayAlias(call, call2)) {

          call match {
            case Equals(_, fin : FunctionInvocation) => functions += 1
            case Equals(_, tup : Tuple) => tuples += 1
            case _ => adts += 1
          }
          if (debugAliases)
            println("Aliases: " + call + "," + call2)

          pairs ++= Set((call, call2))

        } else {
          if (debugAliases) {
            (call, call2) match {
              case (Equals(_, t1 @ Tuple(_)), Equals(_, t2 @ Tuple(_))) =>
                println("No Aliases: " + t1.getType + "," + t2.getType)
              case _ => println("No Aliases: " + call + "," + call2)
            }
          }
        }
      }
      j += 1
      acc ++ pairs
    })
    if(verbose) reporter.info("Number of compatible calls: " + product.size)
    /*reporter.info("Compatible Tuples: "+tuples)
    reporter.info("Compatible Functions+ADTs: "+(functions+adts))*/
    Stats.updateCounterStats(product.size, "Compatible-Calls", "disjuncts")
    Stats.updateCumStats(functions, "Compatible-functioncalls")
    Stats.updateCumStats(adts, "Compatible-adtcalls")
    Stats.updateCumStats(tuples, "Compatible-tuples")
    product
  }

  /**
   * Convert the theory formula into linear arithmetic formula.
   * The calls could be functions calls or ADT constructor calls.
   * 'predEval' is an evaluator that evaluates a predicate to a boolean value
   */
  def constraintsForCalls(calls: Set[Expr], predEval: (Expr => Boolean)): Seq[Expr] = {

    //check if two calls (to functions or ADT cons) have the same value in the model
    def doesAlias(call1: Expr, call2: Expr): Boolean = {
      val Operator(Seq(r1 @ Variable(_), _), _) = call1
      val Operator(Seq(r2 @ Variable(_), _), _) = call2
      val resEquals = predEval(Equals(r1, r2))
      if (resEquals) {
        if (Util.isCallExpr(call1)) {
          val (ants, _) = axiomatizeCalls(call1, call2)
          val antsHold = ants.forall(ant => {
            val Operator(Seq(lvar @ Variable(_), rvar @ Variable(_)), _) = ant
            //(model(lid) == model(rid))
            predEval(Equals(lvar, rvar))
          })
          antsHold
        } else true
      } else false
    }

    def predForEquality(call1: Expr, call2: Expr): Seq[Expr] = {

      val eqs = if (Util.isCallExpr(call1)) {
        val (_, rhs) = axiomatizeCalls(call1, call2)
        Seq(rhs)
      } else {
        val (lhs, rhs) = axiomatizeADTCons(call1, call2)
        lhs :+ rhs
      }
      //remove self equalities.
      val preds = eqs.filter(_ match {
        case Operator(Seq(Variable(lid), Variable(rid)), _) => {
          if (lid == rid) false
          else {
            if (lid.getType == Int32Type || lid.getType == RealType || lid.getType == IntegerType) true
            else false
          }
        }
        case e @ _ => throw new IllegalStateException("Not an equality or Iff: " + e)
      })
      preds
    }

    def predForDisequality(call1: Expr, call2: Expr): Seq[Expr] = {

      val (ants, _) = if (Util.isCallExpr(call1)) {
        axiomatizeCalls(call1, call2)
      } else {
        axiomatizeADTCons(call1, call2)
      }

      if (makeEfficient && ants.exists(_ match {
        case Equals(l, r) if (l.getType != RealType && l.getType != BooleanType && l.getType != IntegerType) => true
        case _ => false
      })) {
        Seq()
      } else {
        var unsatIntEq: Option[Expr] = None
        var unsatOtherEq: Option[Expr] = None
        ants.foreach(eq =>
          if (!unsatOtherEq.isDefined) {
            eq match {
              case Equals(lhs @ Variable(_), rhs @ Variable(_)) if !predEval(Equals(lhs, rhs)) => {
                if (lhs.getType != Int32Type && lhs.getType != RealType && lhs.getType != IntegerType)
                  unsatOtherEq = Some(eq)
                else if (!unsatIntEq.isDefined)
                  unsatIntEq = Some(eq)
              }
              case _ => ;
            }
          })
        if (unsatOtherEq.isDefined) Seq() //need not add any constraint
        else if (unsatIntEq.isDefined) {
          //pick the constraint a < b or a > b that is satisfied
          val Equals(lhs @ Variable(_), rhs @ Variable(_)) = unsatIntEq.get
          val lLTr = LessThan(lhs, rhs)
          val atom = if (predEval(lLTr)) lLTr
          else GreaterThan(lhs, rhs)
          /*val InfiniteIntegerLiteral(lval) = model(lid)
          val InfiniteIntegerLiteral(rval) = model(rid)
          val atom = if (lval < rval) LessThan(lhs, rhs)
          else if (lval > rval) GreaterThan(lhs, rhs)
          else throw new IllegalStateException("Models are equal!!")*/

          /*if (ants.exists(_ match {
              case Equals(l, r) if (l.getType != Int32Type && l.getType != RealType && l.getType != BooleanType && l.getType != IntegerType) => true
              case _ => false
            })) {
              Stats.updateCumStats(1, "Diseq-blowup")
            }*/
          Seq(atom)
        } else throw new IllegalStateException("All arguments are equal: " + (call1, call2))
      }
    }

    var eqGraph = new UndirectedGraph[Expr]() //an equality graph
    var neqSet = Set[(Expr, Expr)]()
    val product = collectCompatibleCalls(calls)
    val newctrs = product.foldLeft(Seq[Expr]())((acc, pair) => {
      val (call1, call2) = (pair._1, pair._2)
      //println("Assertionizing "+call1+" , call2: "+call2)
      if (!eqGraph.BFSReach(call1, call2) && !neqSet.contains((call1, call2)) && !neqSet.contains((call2, call1))) {
        if (doesAlias(call1, call2)) {
          eqGraph.addEdge(call1, call2)
          //note: here it suffices to check for adjacency and not reachability of calls (i.e, exprs).
          //This is because the transitive equalities (corresponding to rechability) are encoded by the generated equalities.
          acc ++ predForEquality(call1, call2)

        } else {
          neqSet ++= Set((call1, call2))
          acc ++ predForDisequality(call1, call2)
        }
      } else acc
    })

    //reporter.info("Number of equal calls: " + eqGraph.getEdgeCount)
    newctrs
  }

  /**
   * This function actually checks if two non-primitive expressions could have the same value
   * (when some constraints on their arguments hold).
   * Remark: notice  that when the expressions have ADT types, then this is basically a form of may-alias check.
   * TODO: handling generic can become very trickier here.
   */
  def mayAlias(e1: Expr, e2: Expr): Boolean = {
    //check if call and call2 are compatible
    /*(e1, e2) match {
      case (Equals(_, FunctionInvocation(fd1, _)), Equals(_, FunctionInvocation(fd2, _))) if (fd1.id == fd2.id) => true
      case (Equals(_, CaseClass(cd1, _)), Equals(_, CaseClass(cd2, _))) if (cd1.id == cd2.id) => true
      case (Equals(_, tp1 @ Tuple(e1)), Equals(_, tp2 @ Tuple(e2))) => {
        //get the types and check if the types are compatible
        val TupleType(tps1) = tp1.getType
        val TupleType(tps2) = tp2.getType
        (tps1 zip tps2).forall(pair => {
          val (t1, t2) = pair
          val lub = TypeOps.leastUpperBound(t1, t2)
          (lub == Some(t1) || lub == Some(t2))
        })
      }
      case _ => false
    }*/
    (e1, e2) match {
      case (Equals(_, FunctionInvocation(fd1, _)), Equals(_, FunctionInvocation(fd2, _))) => {
        (fd1.id == fd2.id && fd1.fd.tparams == fd2.fd.tparams)
      }
      case (Equals(_, CaseClass(cd1, _)), Equals(_, CaseClass(cd2, _))) => {
        // if (cd1.id == cd2.id && cd1.tps != cd2.tps) println("Invalidated the classes " + e1 + " " + e2)
        (cd1.id == cd2.id && cd1.tps == cd2.tps)
      }
      case (Equals(_, tp1 @ Tuple(e1)), Equals(_, tp2 @ Tuple(e2))) => {
        //get the types and check if the types are compatible
        val TupleType(tps1) = tp1.getType
        val TupleType(tps2) = tp2.getType
        (tps1 zip tps2).forall(pair => {
          val (t1, t2) = pair
          val lub = TypeOps.leastUpperBound(t1, t2)
          (lub == Some(t1) || lub == Some(t2))
        })
      }
      case _ => false
    }
  }

  /**
   * This procedure generates constraints for the calls to be equal
   */
  def axiomatizeCalls(call1: Expr, call2: Expr): (Seq[Expr], Expr) = {
    val (v1, fi1, v2, fi2) = {
      val Equals(r1, f1 @ FunctionInvocation(_, _)) = call1
      val Equals(r2, f2 @ FunctionInvocation(_, _)) = call2
      (r1, f1, r2, f2)
    }

    val ants = (fi1.args.zip(fi2.args)).foldLeft(Seq[Expr]())((acc, pair) => {
      val (arg1, arg2) = pair
      acc :+ Equals(arg1, arg2)
    })
    val conseq = Equals(v1, v2)
    (ants, conseq)
  }

  /**
   * The returned pairs should be interpreted as a bidirectional implication
   */
  def axiomatizeADTCons(sel1: Expr, sel2: Expr): (Seq[Expr], Expr) = {

    val (v1, args1, v2, args2) = sel1 match {
      case Equals(r1 @ Variable(_), CaseClass(_, a1)) => {
        val Equals(r2 @ Variable(_), CaseClass(_, a2)) = sel2
        (r1, a1, r2, a2)
      }
      case Equals(r1 @ Variable(_), Tuple(a1)) => {
        val Equals(r2 @ Variable(_), Tuple(a2)) = sel2
        (r1, a1, r2, a2)
      }
    }

    val ants = (args1.zip(args2)).foldLeft(Seq[Expr]())((acc, pair) => {
      val (arg1, arg2) = pair
      acc :+ Equals(arg1, arg2)
    })
    val conseq = Equals(v1, v2)
    (ants, conseq)
  }
}
