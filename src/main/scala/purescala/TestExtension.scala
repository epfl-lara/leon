package purescala

import purescala.Common._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.Definitions._
import purescala.Extensions._

class TestExtension(val reporter: Reporter) extends Analyser(reporter) {
  val description : String = "Testing."
  def analyse(program : Program) : Unit = {
  }/*
    for((f: FunDef) <- program.definedFunctions) {
      reporter.info("Got an f ! " + f.id)
      reporter.info("Normal  : " + f.body.get)
      val iteized = matchToIfThenElse(expandLets(f.body.get))
      reporter.info("ITEized : " + iteized)
      reporter.info("Leadsto ? : " + (leadsToCall(iteized) : String))
      cleanClausify(iteized, program)
      val (e,l,m) = clausifyITE(iteized)
      reporter.info("As clauses : " + e)
      l.foreach(reporter.info(_))
      reporter.info("***\n")
    }
    reporter.info("Done.")
  }*/

  type LiftedBoolean = Option[Boolean]
  val Yes : LiftedBoolean  = Some(true)
  val No : LiftedBoolean = Some(false)
  val Maybe : LiftedBoolean = None
  implicit def bool2liftedbool(b : Boolean) : LiftedBoolean = Some(b)
  implicit def liftedbool2String(l : LiftedBoolean) : String = l match {
    case Yes => "Yes"
    case No => "No"
    case Maybe => "Maybe"
  }

  // assumes no lets and no match.
  def leadsToCall(e : Expr) : LiftedBoolean = e match {
    case f : FunctionInvocation => true
    case IfExpr(a1, a2, a3) => {
      if(leadsToCall(a1) == Yes) Yes else (leadsToCall(a2),leadsToCall(a3)) match {
        case (Yes,Yes) => Yes
        case (No,No) => No
        case _ => Maybe
      }
    }
    case n @ NAryOperator(args, _) => {
      val ra = args.map(leadsToCall(_))
      if(ra.exists(_ == Yes)) {
        Yes
      } else if(ra.forall(_ == No)) {
        No
      } else {
        Maybe
      }
    }
    case b @ BinaryOperator(a1,a2,_) => (leadsToCall(a1),leadsToCall(a2)) match {
      case (Yes,_) => Yes
      case (_,Yes) => Yes
      case (No,No) => No
      case _ => Maybe
    }
    case u @ UnaryOperator(a,_) => leadsToCall(a)
    case t : Terminal => false
    case unhandled => scala.sys.error("unhandled.")
  }

  private def cleanClausify(formula : Expr, program : Program) : Unit = {
    val nonRec = allNonRecursiveFunctionCallsOf(formula, program)
    val allRec = functionCallsOf(formula) -- nonRec

    val (e,l,m) = clausifyITE(formula)
    var dangerSet : Set[Expr] = Set.empty[Expr] ++ allRec
    var change : Boolean = true
    var newSet : Set[Expr] = Set.empty

    while(change) {
      change = false
    }
  }

  private def clausifyITE(formula : Expr) : (Expr, List[Expr], Map[Identifier,Identifier]) = {
    var newClauses : List[Expr] = Nil
    var ite2Bools : Map[Identifier,Identifier] = Map.empty

    def clausify(ex : Expr) : Option[Expr] = ex match {
      //case _ if leadsToCall(ex) == No => None
      case ie @ IfExpr(cond, then, elze) => {
        val switch = FreshIdentifier("path", true).setType(BooleanType).toVariable
        val placeHolder = FreshIdentifier("iteval", true).setType(ie.getType).toVariable
        newClauses = Iff(switch, cond) :: newClauses
        newClauses = Implies(switch, Equals(placeHolder, then)) :: newClauses
        newClauses = Implies(Not(switch), Equals(placeHolder, elze)) :: newClauses
        // newBools = newBools + switch.id
        ite2Bools = ite2Bools + (placeHolder.id -> switch.id)
        Some(placeHolder)
      }
      case _ => None
    }

    val cleanedUp = searchAndReplaceDFS(clausify)(formula)

    (cleanedUp, newClauses.reverse, ite2Bools)
  }
}
