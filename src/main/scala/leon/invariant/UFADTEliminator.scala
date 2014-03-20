package leon
package invariant

import scala.util.Random
import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import solvers.{ Solver, TimeoutSolver }
import solvers.z3.FairZ3Solver
import scala.collection.mutable.{ Set => MutableSet }
import scala.collection.mutable.{ Map => MutableMap }
import leon.evaluators._
import java.io._
import leon.solvers.z3.UninterpretedZ3Solver
import leon.LeonContext
import leon.LeonOptionDef
import leon.LeonPhase
import leon.LeonValueOption
import leon.ListValue
import leon.Reporter
import leon.verification.DefaultTactic
import leon.verification.Tactic
import leon.verification.VerificationReport
import leon.solvers.SimpleSolverAPI
import leon.solvers.z3.UIFZ3Solver
import leon.invariant._
import leon.purescala.UndirectedGraph
import scala.util.control.Breaks._
import leon.solvers._
import leon.purescala.ScalaPrinter
import leon.plugin.DepthInstPhase

class UFADTEliminator(ctx: LeonContext, program: Program) {
 
  val makeEfficient = true //this will happen at the expense of completeness  
  val reporter = ctx.reporter
  
  /**
   * Convert the theory formula into linear arithmetic formula.
   * The calls could be functions calls or ADT constructor calls.
   */  
  def constraintsForCalls(calls: Set[Expr], model: Map[Identifier, Expr]): Seq[Expr] = {

    var eqGraph = new UndirectedGraph[Expr]() //an equality graph
    var neqSet = Set[(Expr, Expr)]()

    //compute the cartesian product of the calls and select the pairs having the same function symbol and also implied by the precond
    val vec = calls.toArray
    val size = calls.size
    var j = 0
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
          pairs ++= Set((call, call2))
        }
      }
      j += 1
      acc ++ pairs
    })
    reporter.info("Number of compatible calls: " + product.size)
    Stats.updateCounterStats(product.size, "Compatible-Calls", "disjuncts")

    //check if two calls (to functions or ADT cons) have the same value in the model 
    def doesAlias(call1: Expr, call2: Expr): Boolean = {
      val BinaryOperator(Variable(r1), _, _) = call1
      val BinaryOperator(Variable(r2), _, _) = call2
      val resEquals = (model(r1) == model(r2))
      if (resEquals) {
        if (InvariantUtil.isCallExpr(call1)) {
          val (ants, _) = axiomatizeCalls(call1, call2)
          val antsHold = ants.forall(ant => {
            val BinaryOperator(Variable(lid), Variable(rid), _) = ant
            (model(lid) == model(rid))
          })
          antsHold
        } else true
      } else false
    }

    def predForEquality(call1: Expr, call2: Expr): Seq[Expr] = {

      val eqs = if (InvariantUtil.isCallExpr(call1)) {        
        val (_, rhs) = axiomatizeCalls(call1, call2)
        Seq(rhs)
      } else {
        val (lhs, rhs) = axiomatizeADTCons(call1, call2)
        lhs :+ rhs
      }
      //remove self equalities. 
      val preds = eqs.filter(_ match {
        case BinaryOperator(Variable(lid), Variable(rid), _) => {
          if (lid == rid) false
          else {
            if (lid.getType == Int32Type || lid.getType == RealType) true
            else false
          }
        }
        case e @ _ => throw new IllegalStateException("Not an equality or Iff: " + e)
      })
      preds
    }

    //TODO: This has an incomplete way of handling ADTs for efficiency. Can this be fixed ?
    def predForDisequality(call1: Expr, call2: Expr): Seq[Expr] = {
      
      val (ants, _) = if (InvariantUtil.isCallExpr(call1)) {
        axiomatizeCalls(call1, call2)
      } else {
        axiomatizeADTCons(call1, call2)
      }

      if (makeEfficient && ants.exists(_ match {
        case Equals(l, r) if (l.getType != Int32Type && l.getType != RealType && l.getType != BooleanType) => true
        case _ => false
      })) {
        Seq()
      } else {
        var unsatIntEq: Option[Expr] = None
        var unsatOtherEq: Option[Expr] = None
        ants.foreach(eq =>
          if (!unsatOtherEq.isDefined) {
            eq match {
              case Equals(lhs @ Variable(_), rhs @ Variable(_)) if (model(lhs.id) != model(rhs.id)) => {
                if (lhs.getType != Int32Type && lhs.getType != RealType)
                  unsatOtherEq = Some(eq)
                else if (!unsatIntEq.isDefined)
                  unsatIntEq = Some(eq)
              }
              case Iff(lhs @ Variable(_), rhs @ Variable(_)) if (model(lhs.id) != model(rhs.id)) =>
                unsatOtherEq = Some(eq)
              case _ => ;
            }
          })
        if (unsatOtherEq.isDefined) Seq() //need not add any constraint
        else if (unsatIntEq.isDefined) {
          //pick the constraint a < b or a > b that is satisfied
          val Equals(lhs @ Variable(lid), rhs @ Variable(rid)) = unsatIntEq.get
          val IntLiteral(lval) = model(lid)
          val IntLiteral(rval) = model(rid)
          val atom = if (lval < rval) LessThan(lhs, rhs)
          else if (lval > rval) GreaterThan(lhs, rhs)
          else throw IllegalStateException("Models are equal!!")

          /*if (ants.exists(_ match {
              case Equals(l, r) if (l.getType != Int32Type && l.getType != RealType && l.getType != BooleanType) => true
              case _ => false
            })) {
              Stats.updateCumStats(1, "Diseq-blowup")
            }*/
          Seq(atom)
        } else throw IllegalStateException("All arguments are equal: " + call1 + " in " + model)
      }
    }
    
    val newctrs = product.foldLeft(Seq[Expr]())((acc, pair) => {
      val (call1, call2) = (pair._1, pair._2)
      //println("Assertionizing "+call1+" , call2: "+call2)      
      if (!eqGraph.BFSReach(call1, call2) && !neqSet.contains((call1, call2)) && !neqSet.contains((call2, call1))) {
        if (doesAlias(call1, call2)) {
          eqGraph.addEdge(call1, call2)
          //note: here it suffices to check for adjacency and not reachability of calls (i.e, exprs).
          //This is because the transitive equalities (corresponding to rechability) are encoded by the generated equalities.
          acc ++ predForEquality(call1, call2)

        } /*else if(this.callsWithAxioms.contains(call1)) {
    	    //is this complete? 
    	     * acc
    	     * }*/ 
        else {
          neqSet ++= Set((call1, call2))
          acc ++ predForDisequality(call1, call2)
        }
      } else acc
    })
    
    reporter.info("Number of equal calls: " + eqGraph.getEdgeCount)
    newctrs
  }
  

  /**
   * This function actually checks if two non-primitive expressions could have the same value
   * (when some constraints on their arguments hold).
   * Remark: notice  that when the expressions have ADT types, then this is basically a form of may-alias check.
   */
  def mayAlias(e1: Expr, e2: Expr): Boolean = {
    //check if call and call2 are compatible
    (e1, e2) match {
      case (Equals(_, FunctionInvocation(fd1, _)), Equals(_, FunctionInvocation(fd2, _))) if (fd1.id == fd2.id) => true
      case (Iff(_, FunctionInvocation(fd1, _)), Iff(_, FunctionInvocation(fd2, _))) if (fd1.id == fd2.id) => true
      case (Equals(_, CaseClass(cd1, _)), Equals(_, CaseClass(cd2, _))) if (cd1.id == cd2.id) => true
      case (Equals(_, tp1 @ Tuple(e1)), Equals(_, tp2 @ Tuple(e2))) if (tp1.getType == tp2.getType) => true
      case _ => false
    }
  }

  /**
   * This procedure generates constraints for the calls to be equal
   */
  def axiomatizeCalls(call1: Expr, call2: Expr): (Seq[Expr], Expr) = {

    val (v1, fi1, v2, fi2) = if (call1.isInstanceOf[Equals]) {
      val Equals(r1, f1 @ FunctionInvocation(_, _)) = call1
      val Equals(r2, f2 @ FunctionInvocation(_, _)) = call2
      (r1, f1, r2, f2)
    } else {
      val Iff(r1, f1 @ FunctionInvocation(_, _)) = call1
      val Iff(r2, f2 @ FunctionInvocation(_, _)) = call2
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
