package orderedsets

import scala.collection.Map
import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}
import purescala.Reporter
import purescala.Extensions.Solver
import Reconstruction.Model

import purescala._
import Trees._
import Common._
import TypeTrees._
import Definitions._

import RPrettyPrinter.rpp

case class IncompleteException(msg: String) extends Exception(msg)

class UnifierMain(reporter: Reporter) extends Solver(reporter) {
  import purescala.Trees._
  import TreeOperations._

  val description = "Unifier for ADTs with abstractions"
  override val shortDescription = "Unifier"

  var program: Program = null

  override def setProgram(p: Program) = program = p

  // checks for V-A-L-I-D-I-T-Y !
  // Some(true) means formula is valid (negation is unsat)
  // Some(false) means formula is not valid (negation is sat)
  // None means you don't know.
  //
  def solve(exprWithLets: Expr): Option[Boolean] = {
    val exprWithIfs = expandLets(exprWithLets)
    val negatedExprWithIfs = negate(exprWithIfs)
    val expr = rewrite(negatedExprWithIfs)
    //println(rpp(expr))
    try {
      var counter = 0
      for (conjunction <- dnf(expr)) {
        counter += 1
        //reporter.info("Solving conjunction " + counter)
        //println(rpp(And(conjunction)))
        try {
          conjunction foreach checkIsSupported
          catamorphism.clear
          // restFormula is also a Sequence of conjunctions
          val (varMap, restFormula) = solve(conjunction)
          // TODO: Might contain multiple c_i ~= {} for a fixed i
          val noAlphas = And(restFormula flatMap expandAlphas(varMap))
          //reporter.info("The resulting formula is\n" + rpp(noAlphas))
          // OrdBAPA finds the formula satisfiable
          if ((new Main(reporter)).solve(ExprToASTConverter(noAlphas))) {
            throw (new SatException(null))
          } else {
            reporter.info("Conjunction " + counter + " is UNSAT, proved by BAPA<")
          }
        } catch {
          case ex@ConversionException(badExpr, msg) =>
            reporter.info("Conjunction " + counter + " is UNKNOWN, could not be parsed")
            throw ex
          case ex@IncompleteException(msg) =>
            reporter.info("Conjunction " + counter + " is UNKNOWN, incomplete")
            throw ex
          //  throw(new IncompleteException("BAPA< cannot handle :" + badExpr + " : " + msg))
          case UnificationImpossible(msg) =>
            reporter.info("Conjunction " + counter + " is UNSAT, proved by Unifier") // (" + msg + ")")
          case ex@SatException(_) =>
            reporter.info("Conjunction " + counter + " is SAT, proved by BAPA<")
            throw ex
        }
      }
      // All conjunctions were UNSAT
      Some(true)
    } catch {
      case ConversionException(badExpr, msg) =>
        reporter.warning(msg + " : " + badExpr.getClass.toString)
        None
      case IncompleteException(msg) =>
        //reporter.info("Unifier cannot disprove this because it is incomplete")
        if (msg != null) reporter.info(msg)
        None
      case SatException(_) =>
        Some(false)
      case e =>
        reporter.error("Component 'Unifier' just crashed.\n  Exception = " + e.toString)
        e.printStackTrace
        None
    } finally {
      Symbol.clearCache
    }
  }

  def checkIsSupported(expr: Expr) {
    def check(ex: Expr): Option[Expr] = ex match {
      case Let(_, _, _) | MatchExpr(_, _) =>
        throw ConversionException(ex, "Unifier does not support this expression")
      case IfExpr(_, _, _) =>
       
       println
       println("--- BEFORE ---")
       println(rpp(expr))
       println
       println("--- AFTER ---")
       println(rpp(rewrite(expr)))
       println
         
      
        throw ConversionException(ex, "Unifier does not support this expression")
      case _ => None
    }
    searchAndReplace(check)(expr)
  }


  /* Returns a conjunction which contains the rest of the formula
  * apart from the ADTs
  */
  def solve(conjunction: Seq[Expr]): (Variable => Expr, Seq[Expr]) = {
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

    (subst, rest)

  }

  /* Step 1 : Do DNF transformation (done elsewhere) */

  /* Step 2 : Split conjunction into (FT, Rest) purifying terms if needed.
  * FT are equations over ADT trees.
  * We allow element variables to appear in FT.
  * Later, we will also allow element variables to appear in FT,
  * but this has not been implemented yet.
  */

  import scala.collection.mutable.{Stack, ArrayBuffer}
  import purescala._
  import Common.FreshIdentifier
  import TypeTrees.Typed

  def freshVar(prefix: String, typed: Typed) = Variable(FreshIdentifier(prefix, true) setType typed.getType)


  def separateADT(conjunction: Seq[Expr]) = {
    val workStack = Stack(conjunction.reverse: _*)
    val good = new ArrayBuffer[Expr]() // Formulas over ADTs
    val bad = new ArrayBuffer[Expr]() // Formulas of unknown logic
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

  /* Step 4 : Partial evaluation of catamorphisms */
  def isAlpha(substArg: Expr => Expr)(expr: Expr): Option[Expr] = expr match {
    case FunctionInvocation(fd, Seq(arg)) => asCatamorphism(program, fd) match {
      case Some(lstMatch) => substArg(arg) match {
        case t@Variable(_) => {
          Some(evalCatamorphism(t, fd, expr))
        }
        case CaseClass(cd, args) => {
          val (_, _, ids, rhs) = lstMatch.find(_._1 == cd).get
          val repMap = Map(ids.map(id => Variable(id): Expr).zip(args): _*)
          //reporter.warning("Converting\n" + rpp(expr) + " to " + rpp(rhs))
          val res = searchAndReplace(repMap.get)(rhs)
          //reporter.warning("Result:\n" + rpp(res))
          Some(res)
        }
        case _ => error("Bad argument/substitution to catamorphism")
      }
      case None => // Not a catamorphism
        warning("Function " + fd.id + " is not a catamorphism.")
        None
    //error("Not a catamorphism.")
    }
    case _ => None // not a function invocation
  }

  def substFunArg(varMap: Variable => Expr)(expr: Expr) = expr match {
    case v@Variable(_) => varMap(v)
    case _ => expr
  }


  val displayedWarnings = MutableSet[String]()

  def warning(text: String) {
    if (!displayedWarnings(text)) {
      displayedWarnings(text) = true
      reporter.warning(text)
    }
  }


  private val catamorphism = MutableMap[(Variable, FunDef), Variable]()

  def evalCatamorphism(v: Variable, fd: FunDef, collType: Typed) = catamorphism get ((v, fd)) match {
    case Some(c) => c
    case None =>
      val c = freshVar("Coll", collType)
      catamorphism((v, fd)) = c
      c
  }

  def expandAlphas(varMap: Variable => Expr)(expr: Expr): Seq[Expr] = {
    //catamorphism.clear
    val partiallyEvaluated = searchAndReplace(isAlpha(substFunArg(varMap)))(expr)
    if (partiallyEvaluated == expr) {
      //reporter.warning(rpp(expr) + "\ndoes not contain any catamorphism.")
      Seq(expr) // Not a catamorphism
    }
    else { // partiallyEvaluated is the Partially evaluated expression
      //reporter.warning(rpp(expr) + "\n found to contain one or more catamorphisms. Translated to:\n" + rpp(partiallyEvaluated))
      var conjuncts = Seq(partiallyEvaluated)
      // SetEquals or just Equals?
      //searchAndReplace({case v@Variable(_) => nonEmptySetsExpr :+= Not(SetEquals(v, EmptySet(v.getType))); None; case _ => None})(partiallyEvaluated)

      // for (svar <- catamorphism.values; if hasSetType(svar))
      //   conjuncts :+= Not(SetEquals(svar, EmptySet(svar.getType)))
      //catamorphism.clear

      /*
      println("--- catamorphism ---")
      for (((t, fd), c) <- catamorphism)
        println(fd.id + "( " + t + " )  =  " + c)
      println
      */

      conjuncts
    }
  }

  def hasSetType(typed: Typed) = typed.getType match {
    case SetType(_) => true
    case _ => false
  }
}
