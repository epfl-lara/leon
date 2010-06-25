package orderedsets

import purescala.Reporter
import purescala.Extensions.Solver
//import Phase3._
//import Reconstruction._
//import Primitives._
import Reconstruction.ReconstructedValues

class Main(reporter: Reporter) extends Solver(reporter) {
  import ExprToASTConverter.ConversionException
  import purescala.Trees.Expr
  import AST.Formula
  import Phase3.EquiClass

  val description = "BAPA with ordering"


  // checks for V-A-L-I-D-I-T-Y !
  // Some(true) means formula is valid (negation is unsat)
  // None means you don't know.
  def solve(expr: Expr): Option[Boolean] = {
    try {
      Some(!solve(!ExprToASTConverter(expr)))
    } catch {
      case ConversionException(badExpr, msg) =>
        reporter.info(badExpr, "BAPA")
        None
      case e =>
        reporter.error("BAPA with ordering just crashed.\n  exception = " + e.toString)
        None
    } finally {
      Symbol.clearCache
    }
  }

  // checks for U-N-S-A-T-I-S-F-I-A-B-I-L-I-T-Y !
  // true means formula is SAT
  // false means formula is UNSAT
  private def solve(formula: Formula): Boolean = {
    val form = NormalForms.nnf(formula)
    val outIntVars = ASTUtil.intvars(form).toList
    val outSetVars = ASTUtil.setvars(form).toList
    var model: Option[ReconstructedValues] = None

    def callZ3(z3: MyZ3Context, paForm: Formula, eqClasses: List[EquiClass]) {
      z3.push
      z3.impose(paForm)

      val result = z3.getModel match {
        case s@Sat(deleteModel, bools, ints) => {
          val model = Reconstruction.getReconstruction(s, outSetVars, outIntVars, eqClasses)
          deleteModel()
          throw new SatException(model)
        }
        case Unsat =>
        case Z3Failure(e) =>
          reporter.fatalError("Z3 not executed:  " + e)
      }
      z3.pop
    }

    reporter.info("BAPA< formula to be verified:\n" + form.toString)

    val z3 = new MyZ3Context
    val start = System.nanoTime
    try {
      for (conj <- NormalForms(form)) {
        z3.push
        //println("Conjunction:")
        //conj.print
        try {
          Phase2(Phase3(callZ3))(z3, conj)
        } catch {
          case Phase2.UnsatException(msg) =>
        }
        z3.pop
      }
    } catch {
      case SatException(_model) =>
        model = Some(_model)
    } finally {
      z3.delete
    }
    val end = System.nanoTime
    var toReturn: Boolean = false
    val total = ((end - start) / 1000000) / 1000.0

    model match {
      case Some(ReconstructedValues(intMap, setMap)) =>
        reporter.info("Counter-example found :")
        intMap.toList.sortWith {_._1.name < _._1.name}.foreach(x => reporter.info("\t\t " + x._1.toString + " -> " + x._2))
        setMap.toList.sortWith {_._1.name < _._1.name}.foreach(x => reporter.info("\t\t " + x._1.toString + " -> " + x._2.toList.sortWith {_ < _}.mkString("Set { ", ", ", " }")))
        reporter.info("Total time : " + total)
        true
      case None =>
        reporter.info("Total time : " + total)
        false
    }
  }
}

case class SatException(model: ReconstructedValues) extends RuntimeException("A model was found")

object ExprToASTConverter {
  import purescala.TypeTrees._
  import purescala.Trees._
  import Primitives._

  case class ConversionException(expr: Expr, msg: String) extends RuntimeException(msg)

  private def toSetTerm(expr: Expr): AST.Term = expr match {
    case Variable(id) if id.getType == SetType(Int32Type) => Symbol(id.name, Symbol.SetType)
    case EmptySet(_) => AST.emptyset
    case FiniteSet(elems) => AST.Op(UNION, (elems map toIntTerm map {_.singleton}).toList)
    case SetCardinality(set) => toSetTerm(set).card
    case SetIntersection(set1, set2) => toSetTerm(set1) ** toSetTerm(set2)
    case SetUnion(set1, set2) => toSetTerm(set1) ++ toSetTerm(set2)
    case SetDifference(set1, set2) => toSetTerm(set1) -- toSetTerm(set2)
    case _ => throw ConversionException(expr, "Cannot convert to bapa< set term")
  }

  private def toIntTerm(expr: Expr): AST.Term = expr match {
    case Variable(id) if id.getType == Int32Type => Symbol(id.name, Symbol.IntType)
    case IntLiteral(v) => AST.Lit(IntLit(v))
    case Plus(lhs, rhs) => toIntTerm(lhs) + toIntTerm(rhs)
    case Minus(lhs, rhs) => toIntTerm(lhs) - toIntTerm(rhs)
    case Times(lhs, rhs) => toIntTerm(lhs) * toIntTerm(rhs) // TODO: check linearity ?
    case UMinus(e) => AST.zero - toIntTerm(e)
    case SetCardinality(e) => toSetTerm(e).card
    case SetMin(set) => toSetTerm(set).inf
    case SetMax(set) => toSetTerm(set).sup
    case _ => throw ConversionException(expr, "Cannot convert to bapa< int term")
  }

  private def toFormula(expr: Expr): AST.Formula = expr match {
    case BooleanLiteral(true) => AST.True
    case BooleanLiteral(false) => AST.False
    case Variable(id) if id.getType == BooleanType => Symbol(id.name, Symbol.BoolType)
    case Or(exprs) => AST.Or((exprs map toFormula).toList)
    case And(exprs) => AST.And((exprs map toFormula).toList)
    case Not(expr) => !toFormula(expr)
    case Implies(expr1, expr2) => !(toFormula(expr1)) || toFormula(expr2)

    // Set Formulas
    case ElementOfSet(elem, set) => toIntTerm(elem) selem toSetTerm(set)
    case SetEquals(set1, set2) => toSetTerm(set1) seq toSetTerm(set2)
    case IsEmptySet(set) => toSetTerm(set).card === 0
    case SubsetOf(set1, set2) => toSetTerm(set1) subseteq toSetTerm(set2)

    // Integer Formulas
    case LessThan(lhs, rhs) => toIntTerm(lhs) < toIntTerm(rhs)
    case LessEquals(lhs, rhs) => toIntTerm(lhs) <= toIntTerm(rhs)
    case GreaterThan(lhs, rhs) => toIntTerm(lhs) > toIntTerm(rhs)
    case GreaterEquals(lhs, rhs) => toIntTerm(lhs) >= toIntTerm(rhs)
    case Equals(lhs, rhs) => toIntTerm(lhs) === toIntTerm(rhs)

    case _ => throw ConversionException(expr, "Cannot convert to bapa< formula")
  }

  def apply(expr: Expr) = toFormula(expr)
}