package orderedsets

import scala.collection.Map
import purescala.Reporter
import purescala.Extensions.Solver
import Reconstruction.Model

case class IncompleteException(msg: String) extends Exception(msg)

class UnifierMain(reporter: Reporter) extends Solver(reporter) {
  import purescala.Trees._
  import TreeOperations._

  val description = "Unifier for ADTs with abstractions"
  override val shortDescription = "Unifier"

  // checks for V-A-L-I-D-I-T-Y !
  // Some(true) means formula is valid (negation is unsat)
  // Some(false) means formula is not valid (negation is sat)
  // None means you don't know.
  //
  def solve(exprWithLets: Expr): Option[Boolean] = {
    val expr = expandLets(exprWithLets)
    try {
      var counter = 0
      for (conjunction <- dnf(negate(expr))) {
        counter += 1
        reporter.info("Solving conjunction " + counter)
        //conjunction foreach println
        conjunction foreach checkIsSupported
        try {
          solve(conjunction)
        } catch {        
          case UnificationImpossible(msg) =>
            reporter.info("Conjunction " + counter + " is UNSAT, unification impossible : " + msg)
        }
      }
      // All conjunctions were UNSAT
      Some(true)
    } catch {
      case ConversionException(badExpr, msg) =>
        reporter.info(msg + " : " + badExpr.getClass.toString)
//        reporter.info(DNF.pp(badExpr))
        //error("should not happen")
        None
      case IncompleteException(msg) =>
        reporter.info("Unifier cannot disprove this because it is incomplete")
        if (msg != null) reporter.info(msg)
        None
      case SatException(_) =>
        Some(false)
      case e =>
        reporter.error("Component 'Unifier' just crashed.\n  Exception = " + e.toString)
        e.printStackTrace
        None
    } finally {
      
    }
  }
  
  def checkIsSupported(expr: Expr) {
    def check(ex: Expr): Option[Expr] = ex match {
      case IfExpr(_, _, _) | Let(_, _, _) | MatchExpr(_, _) =>
        throw ConversionException(ex, "Not supported")
      case _ => None
    }
    searchAndReplace(check)(expr)
  }

  
  def solve(conjunction: Seq[Expr]) {
    val (treeEquations, rest) = separateADT(conjunction)
    
    /*
    reporter.info("Fc")
    treeEquations  foreach println
    reporter.info("Rest")
    rest foreach println
    */
    
    // The substitution table
    val substTable = ADTUnifier.unify(treeEquations)
    
    // The substitution function (returns identity if unmapped)
    def subst(v: Variable): Expr = substTable getOrElse (v, v)
    
    throw IncompleteException(null)
    
    ()
  }
  
  /* Step 1 : Do DNF transformation (done elsewhere) */
  
  /* Step 2 : Split conjunction into (FT, Rest) purifying terms if needed.
   * FT are equations over ADT trees.
   * We allow element variables to appear in FT.
   * Later, we will also allow element variables to appear in FT,
   * but this has not been implemented yet.
   */
   
  import scala.collection.mutable.{Stack,ArrayBuffer}
  import purescala._
  import Common.FreshIdentifier
  import TypeTrees.Typed
   
  def freshVar(prefix: String, typed: Typed) = Variable(FreshIdentifier(prefix, true) setType typed.getType)
  
  
  def separateADT(conjunction: Seq[Expr]) = {
    val workStack = Stack(conjunction.reverse: _*)
    val good = new ArrayBuffer[Expr]() // Formulas over ADTs
    val bad = new ArrayBuffer[Expr]()  // Formulas of unknown logic
    // TODO: Allow literals in unifier ?
    def isGood(expr: Expr) = expr match {
      case Variable(_) | CaseClass(_, _) | CaseClassSelector(_, _) => true
      case _ => false
    }
    def isBad(expr: Expr) = expr match {
      case CaseClass(_, _) | CaseClassSelector(_, _) => false
      case _ => true
    }
    def purifyGood(expr: Expr) = if (isGood(expr)) None else {
      val fresh = freshVar("col", expr)
      workStack push Equals(fresh, expr) // will be bad
//      println("PUSH bad  : " + isBad(expr) + "  " +  expr)
      Some(fresh)
    }
    def purifyBad(expr: Expr) = if (isBad(expr)) None else {
      val fresh = freshVar("adt", expr)
      workStack push Equals(fresh, expr) // will be good
//      println("PUSH good : " + isGood(expr) + "  " + expr)
      Some(fresh)
    }
    def process(expr: Expr): Unit = expr match {
      case Equals(t1, t2) if isGood(t1) && isGood(t2) =>
//      println("POP good  :       " + expr)
        val g1 = searchAndReplace(purifyGood)(t1)
        val g2 = searchAndReplace(purifyGood)(t2)
        good += Equals(g1, g2)
//        println("ADD good  :       " + Equals(g1, g2))
      case Not(Equals(t1, t2)) if isGood(t1) && isGood(t2) =>
//      println("POP good2 :       " + expr)
        val g1 = searchAndReplace(purifyGood)(t1)
        val g2 = searchAndReplace(purifyGood)(t2)
        good += Not(Equals(g1, g2))
//        println("ADD good2 :       " + Not(Equals(g1, g2)))
      case Not(Not(ex)) =>
        process(ex)
      case _ => 
//      println("POP bad   :       " + expr)
        val t = searchAndReplace(purifyBad)(expr)
        bad += t
//        println("ADD bad   :       " + t)
    }
    while (!workStack.isEmpty) {
      val expr = workStack.pop
      process(expr)
    }
    (good.toSeq, bad.toSeq)
  }
  
  /* Step 3 : Perform unifcation on equations over ADTs.
   * Obtain a substitution u = T(t) and 
   * disequalites N(u,t) over ADT variables, and
   * get implied (dis)equalities FE over element variables.
   */
}
