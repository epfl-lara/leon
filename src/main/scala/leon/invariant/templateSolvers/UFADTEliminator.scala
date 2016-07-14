/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.templateSolvers

import purescala.Definitions._
import purescala.Expressions._
import purescala.Extractors._
import purescala.Types._
import invariant.datastructure._
import invariant.util._
import leon.purescala.TypeOps
import PredicateUtil._
import Stats._
import scala.collection.mutable.{ Set => MutableSet, Map => MutableMap, MutableList }

class UFADTEliminator(ctx: LeonContext, program: Program) {

  val debugAliases = false
  val makeEfficient = true //this will happen at the expense of completeness
  val reporter = ctx.reporter
  val verbose = false

  //  def collectCompatibleCalls(calls: Set[Expr]) = {
  //    //compute the cartesian product of the calls and select the pairs having the same function symbol and also implied by the precond
  //    val vec = calls.toArray
  //    val size = calls.size
  //    var j = 0
  //    //for stats
  //    var tuples = 0
  //    var functions = 0
  //    var adts = 0
  //    val product = vec.foldLeft(Set[(Expr, Expr)]())((acc, call) => {
  //      //an optimization: here we can exclude calls to maxFun from axiomatization, they will be inlined anyway
  //      /*val shouldConsider = if(InvariantisCallExpr(call)) {
  //        val BinaryOperator(_,FunctionInvocation(calledFun,_), _) = call
  //        if(calledFun == DepthInstPhase.maxFun) false
  //        else true
  //      } else true*/
  //      var pairs = Set[(Expr, Expr)]()
  //      for (i <- j + 1 until size) {
  //        val call2 = vec(i)
  //        if (mayAlias(call, call2)) {
  //          call match {
  //            case Equals(_, fin: FunctionInvocation) => functions += 1
  //            case Equals(_, tup: Tuple)              => tuples += 1
  //            case _                                  => adts += 1
  //          }
  //          if (debugAliases)
  //            println("Aliases: " + call + "," + call2)
  //          pairs ++= Set((call, call2))
  //        } else {
  //          if (debugAliases) {
  //            (call, call2) match {
  //              case (Equals(_, t1 @ Tuple(_)), Equals(_, t2 @ Tuple(_))) =>
  //                println("No Aliases: " + t1.getType + "," + t2.getType)
  //              case _ => println("No Aliases: " + call + "," + call2)
  //            }
  //          }
  //        }
  //      }
  //      j += 1
  //      acc ++ pairs
  //    })
  //    if (verbose) reporter.info("Number of compatible calls: " + product.size)
  //    Stats.updateCounterStats(product.size, "Compatible-Calls", "disjuncts")
  //    Stats.updateCumStats(functions, "Compatible-functioncalls")
  //    Stats.updateCumStats(adts, "Compatible-adtcalls")
  //    Stats.updateCumStats(tuples, "Compatible-tuples")
  //    product
  //  }

  def collectCompatibleTerms(terms: Set[Expr]) = {
    class Comp(val key: Either[TypedFunDef, TypeTree]) {
      override def equals(other: Any) = other match {
        case otherComp: Comp => mayAlias(key, otherComp.key)
        case _               => false
      }
      // an weaker property whose equality is necessary for mayAlias
      val hashcode =
        (key: @unchecked) match {
          case Left(TypedFunDef(fd, _))   => fd.id.hashCode()
          case Right(ct: CaseClassType)   => ct.classDef.id.hashCode()
          case Right(tp @ TupleType(tps)) => (tps.hashCode() << 3) ^ tp.dimension
        }
      override def hashCode = hashcode
    }
    val compTerms = MutableMap[Comp, MutableList[Expr]]()
    terms.foreach { term =>
      //an optimization: here we can exclude calls to maxFun from axiomatization, they will be inlined anyway
      /*val shouldConsider = if(InvariantisCallExpr(call)) {
        val BinaryOperator(_,FunctionInvocation(calledFun,_), _) = call
        if(calledFun == DepthInstPhase.maxFun) false
        else true
      } else true*/
      val compKey: Either[TypedFunDef, TypeTree] = term match {
        case Equals(_, rhs) => rhs match { // tuple types require special handling before they are used as keys
          case tp: Tuple =>
            val TupleType(tps) = tp.getType
            Right(TupleType(tps.map { TypeOps.bestRealType }))
          case FunctionInvocation(tfd, _) => Left(tfd)
          case CaseClass(ct, _)           => Right(ct)
        }
      }
      val comp = new Comp(compKey)
      val compList = compTerms.getOrElse(comp, {
        val newl = new MutableList[Expr]()
        compTerms += (comp -> newl)
        newl
      })
      compList += term
    }
    if (debugAliases) {
      compTerms.foreach {
        case (_, v) => println("Aliases: " + v.mkString("{", ",", "}"))
      }
    }
    compTerms
  }

  /**
   * Convert the theory formula into linear arithmetic formula.
   * The calls could be functions calls or ADT constructor calls.
   * 'predEval' is an evaluator that evaluates a predicate to a boolean value
   * TODO: is type parameter inheritance handled correctly ?
   */
  def constraintsForCalls(calls: Set[Expr], predEval: (Expr => Option[Boolean])): Seq[Expr] = {

    //check if two calls (to functions or ADT cons) have the same value in the model
    def doesAlias(call1: Expr, call2: Expr): Option[Boolean] = {
      val Operator(Seq(r1 @ Variable(_), _), _) = call1
      val Operator(Seq(r2 @ Variable(_), _), _) = call2
      predEval(Equals(r1, r2)) match {
        case Some(true) if isCallExpr(call1) =>
          val (ants, _) = axiomatizeCalls(call1, call2)
          val antsEvals = ants.map(ant => {
            val Operator(Seq(lvar @ Variable(_), rvar @ Variable(_)), _) = ant
            predEval(Equals(lvar, rvar))
          })
          // return `false` if at least one argument is false
          if (antsEvals.exists(_ == Some(false))) Some(false)
          else if (antsEvals.exists(!_.isDefined)) None // here, we cannot decide if the call is true or false
          else Some(true)
        case r => r
      }
    }

    def predForEquality(call1: Expr, call2: Expr): Seq[Expr] = {
      val eqs = if (isCallExpr(call1)) {
        val (_, rhs) = axiomatizeCalls(call1, call2)
        Seq(rhs)
      } else {
        val (lhs, rhs) = axiomatizeADTCons(call1, call2)
        lhs :+ rhs
      }
      //remove self equalities.
      val preds = eqs.filter {
        case Operator(Seq(Variable(lid), Variable(rid)), _) => {
          if (lid == rid) false
          else {
            if (lid.getType == Int32Type || lid.getType == RealType || lid.getType == IntegerType) true
            else false
          }
        }
        case e @ _ => throw new IllegalStateException("Not an equality or Iff: " + e)
      }
      preds
    }

    def predForDisequality(call1: Expr, call2: Expr): Seq[Expr] = {
      val (ants, _) = if (isCallExpr(call1)) {
        axiomatizeCalls(call1, call2)
      } else {
        axiomatizeADTCons(call1, call2)
      }
      if (makeEfficient && ants.exists {
        case Equals(l, r) if (l.getType != RealType && l.getType != BooleanType && l.getType != IntegerType) => true
        case _ => false
      }) {
        Seq()
      } else {
        var unsatIntEq: Option[Expr] = None
        var unsatOtherEq: Option[Expr] = None
        ants.foreach(eq =>
          if (unsatOtherEq.isEmpty) {
            eq match {
              case Equals(lhs @ Variable(_), rhs @ Variable(_)) if predEval(Equals(lhs, rhs)) == Some(false) => { // there must exist at least one such predicate
                if (lhs.getType != Int32Type && lhs.getType != RealType && lhs.getType != IntegerType)
                  unsatOtherEq = Some(eq)
                else if (unsatIntEq.isEmpty)
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
          predEval(lLTr) match {
            case Some(true)  => Seq(lLTr)
            case Some(false) => Seq(GreaterThan(lhs, rhs))
            case _           => Seq() // actually this case cannot happen.
          }
        } else throw new IllegalStateException("All arguments are equal: " + (call1, call2))
      }
    }

    var equivClasses = new DisjointSets[Expr]()
    var neqSet = MutableSet[(Expr, Expr)]()
    val termClasses = collectCompatibleTerms(calls)
    val preds = MutableList[Expr]()
    termClasses.foreach {
      case (_, compTerms) =>
        val vec = compTerms.toArray
        val size = vec.size
        vec.zipWithIndex.foreach {
          case (t1, j) =>
            (j + 1 until size).foreach { i =>
              val t2 = vec(i)
              if (compatibleTArgs(termTArgs(t1), termTArgs(t2))) {
                //note: here we omit constraints that encode transitive equality facts
                val class1 = equivClasses.findOrCreate(t1)
                val class2 = equivClasses.findOrCreate(t2)
                if (class1 != class2 && !neqSet.contains((t1, t2)) && !neqSet.contains((t2, t1))) {
                  doesAlias(t1, t2) match {
                    case Some(true) =>
                      equivClasses.union(class1, class2)
                      preds ++= predForEquality(t1, t2)
                    case Some(false) =>
                      neqSet ++= Set((t1, t2))
                      preds ++= predForDisequality(t1, t2)
                    case _ =>
                    // in this case, we construct a weaker disjunct by dropping this predicate                      
                  }
                }
              }
            }
        }
    }   
    Stats.updateCounterStats(preds.size, "CallADT-Constraints", "disjuncts")
    preds.toSeq
  }

  def termTArgs(t: Expr) = {
    t match {
      case Equals(_, e) =>
        e match {
          case FunctionInvocation(TypedFunDef(_, tps), _) => tps
          case CaseClass(ct, _)                           => ct.tps
          case tp: Tuple =>
            val TupleType(tps) = tp.getType
            tps
        }
    }
  }

  /**
   * This function actually checks if two non-primitive expressions could have the same value
   * (when some constraints on their arguments hold).
   * Remark: notice  that when the expressions have ADT types, then this is basically a form of may-alias check.
   * TODO: handling type parameters can become very trickier here.
   * For now ignoring type parameters of functions and classes. (This is complete, but may be less efficient)
   */
  def mayAlias(term1: Either[TypedFunDef, TypeTree], term2: Either[TypedFunDef, TypeTree]): Boolean = {
    (term1, term2) match {
      case (Left(TypedFunDef(fd1, _)), Left(TypedFunDef(fd2, _))) =>
        fd1.id == fd2.id
      case (Right(ct1: CaseClassType), Right(ct2: CaseClassType)) =>
        ct1.classDef.id == ct2.classDef.id
      case (Right(tp1 @ TupleType(tps1)), Right(tp2 @ TupleType(tps2))) if tp1.dimension == tp2.dimension =>
        compatibleTArgs(tps1, tps2) //get the types and check if the types are compatible
      case _ => false
    }
  }

  def compatibleTArgs(tps1: Seq[TypeTree], tps2: Seq[TypeTree]): Boolean = {
    (tps1 zip tps2).forall {
      case (t1, t2) =>
        val lub = TypeOps.leastUpperBound(t1, t2)
        (lub == Some(t1) || lub == Some(t2)) // is t1 a super type of t2
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
