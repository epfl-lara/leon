package orderedsets

import purescala.Reporter
import Phase3._
import Reconstruction._
import purescala.TypeTrees._
import purescala.Common._
import purescala.Extensions._
import purescala.Trees._
import Primitives._

class Main(reporter: Reporter) extends Solver(reporter) {
  val description = "Solver for constraints on ordered sets"

  def convertToSetTerm( expr : Expr ): AST.Term = expr match {
    // TODO: Use id.getType as Symbol's type, this _has_ to be a set variable
    case Variable(id) if id.getType == SetType(Int32Type) => Symbol(id.name, Symbol.SetType) 
    case EmptySet(_) => AST.emptyset
    case FiniteSet(elems) => AST.Op(UNION, ( elems map convertToIntTerm map {_.singleton} ).toList)
    case SetCardinality(set) => convertToSetTerm(set).card
    case SetIntersection(set1, set2) => convertToSetTerm(set1) ** convertToSetTerm(set2)
    case SetUnion(set1, set2) => convertToSetTerm(set1) ++ convertToSetTerm(set2)
    // TODO: Confirm the order of operation
    case SetDifference(set1, set2) => convertToSetTerm(set1) -- convertToSetTerm(set2)
    case SetMin(set) => convertToSetTerm(set).inf
    case SetMax(set) => convertToSetTerm(set).sup
    case _ =>  reporter.error(expr, "Not a Set expression!"); error("Not a Set expression!") 
  }

  def convertToIntTerm( expr : Expr ): AST.Term = expr match {
    case IntLiteral(v) => AST.Lit(IntLit(v))
    case Variable(id) if id.getType == Int32Type => Symbol(id.name, Symbol.IntType) 
    case Plus(lhs, rhs) => convertToIntTerm(lhs) + convertToIntTerm(rhs)
    // TODO: Confirm order of operation
    case Minus(lhs, rhs) => convertToIntTerm(lhs) - convertToIntTerm(rhs)
    // TODO: Checking for linearity?
    case Times(lhs, rhs) => convertToIntTerm(lhs) * convertToIntTerm(rhs)
    // TODO: Throwing own exception here?
    case Division(_, _) => reporter.error(expr, "Division is not supported."); error("Division is not supported.")
    case UMinus(e) => AST.zero - convertToIntTerm(e)
    case SetCardinality(e) => convertToSetTerm(e).card
    case _ => reporter.error(expr, "Not an integer expression!"); error("Not an integer expression.")
  }

  def convertToAST( expr : Expr ): AST.Formula = expr match {
    case BooleanLiteral(true) => AST.True
    case BooleanLiteral(false) => AST.False
    // TODO: Use id.getType as Symbol's type, this _has_ to be a set variable
    case Variable(id) if id.getType == BooleanType => Symbol(id.name, Symbol.BoolType)

    case Or(exprs) => AST.Or((exprs map convertToAST).toList)
    case And(exprs) => AST.And((exprs map convertToAST).toList)
    case Not(expr) => !convertToAST(expr)
    case Implies(expr1, expr2) => !(convertToAST(expr1)) || convertToAST(expr2)

    // Set Formulas
    case ElementOfSet(elem, set) => convertToIntTerm(elem) selem convertToSetTerm(set)
    case SetEquals(set1, set2) => convertToSetTerm(set1) seq convertToSetTerm(set2)
    // Is this a formula or a boolean function? Purification?
    // TODO: Nicer way to write this?
    // case IsEmptySet(set) => AST.Op(ITE, (convertToSetTerm(set).card === 0)::AST.True::AST.False::Nil)
    case IsEmptySet(set) => convertToSetTerm(set).card === 0
    case SubsetOf(set1, set2) => convertToSetTerm(set1) subseteq convertToSetTerm(set2)

    // Integer Formulas
    case LessThan(lhs, rhs) => convertToIntTerm(lhs) < convertToIntTerm(rhs)
    case LessEquals(lhs, rhs) => convertToIntTerm(lhs) <= convertToIntTerm(rhs)
    case GreaterThan(lhs, rhs) => convertToIntTerm(lhs) > convertToIntTerm(rhs)
    case GreaterEquals(lhs, rhs) => convertToIntTerm(lhs) >= convertToIntTerm(rhs)
    case Equals(lhs, rhs) => convertToIntTerm(lhs) === convertToIntTerm(rhs)

    case _ => reporter.error(expr, "Cannot be handled by Ordered BAPA."); error("Cannot be handled")
  }

  var allModels: Set[ReconstructedValues] = Set()
  var outSetVars: Set[Symbol] = null
  var outIntVars: Set[Symbol] = null

  def callZ3(z3: MyZ3Context, paForm: AST.Formula, eq: List[EquiClass]): Phase2.Hint = {

    z3.push
    z3.impose(paForm)

    val result = z3.getModel match {
      case s@Sat(deleteModel, bools, ints) => {
        reporter.info("Formula satisfiable")
        allModels += Reconstruction.getReconstruction(s, outSetVars.toList, outIntVars.toList, eq)
        deleteModel()
        true
      }
      case Unsat => reporter.info("Formula unsatisfiable"); false
      case Z3Failure(e) => error("Z3 not executed.  " + e);
    }
    z3.pop
    result
  }

  // checks for V-A-L-I-D-I-T-Y !
  // Some(true) means formula is valid (negation is unsat)
  // None means you don't know.
  def solve(expr: Expr) : Option[Boolean] = {
    try {
      val form = NormalForms.nnf(convertToAST(expr))
      outIntVars = ASTUtil.intvars(form)
      outSetVars = ASTUtil.setvars(form)

      reporter.info("OrdBAPA conversion = " + form.toString)
      val start = System.nanoTime
      for (conj <- NormalForms(!form)) {
        //println("Conjunction:")
        //conj.print
        try {
            Phase2(Phase3.segment(callZ3))(conj)
        } catch {
          case Phase2.UnsatException(msg) =>
            reporter.error("  " + msg)
        }
      }
      val end = System.nanoTime
      var toReturn : Boolean = false
      val total = ((end - start) / 1000000) / 1000.0
      if (!allModels.isEmpty) {
        reporter.info("Models after reconstruction:")
        toReturn = true
      } else {
        toReturn = false
      }
        
      for (ReconstructedValues(intMap, setMap) <- allModels) {

        intMap.toList.sortWith {_._1.name < _._1.name}.foreach(x => reporter.info("\t\t " + x._1.toString + " -> " + x._2))
        setMap.toList.sortWith {_._1.name < _._1.name}.foreach(x => reporter.info("\t\t " + x._1.toString + " -> " + x._2.toList.sortWith {_ < _}.mkString("Set { ", ", ", " }")))
      }

      reporter.info("Total time : " + total)
      Some(!toReturn)
    } catch {
      case e => 
        reporter.info("OrdBAPA exception = " + e.toString)
        reporter.info(expr, "OrdBAPA has no idea how to solve this :(")
        None
    }
  }
}
