package orderedsets

import purescala.Reporter
import purescala.Extensions.Solver
import Reconstruction.Model

class Main(reporter: Reporter) extends Solver(reporter) {
  import ExprToASTConverter.ConversionException
  import purescala.Trees.Expr
  import AST.Formula
  val description = "BAPA with ordering"

  // checks for V-A-L-I-D-I-T-Y !
  // Some(true) means formula is valid (negation is unsat)
  // Some(false) means formula is not valid (negation is sat)
  // None means you don't know.
  //
  // If the formula was found to be not valid,
  // a counter-example is displayed (i.e. the model for negated formula)
  def solve(expr: Expr): Option[Boolean] = {
    reporter.info("Sets: " + ExprToASTConverter.getSetTypes(expr))
    try {
      // Negate formula
      (Some(!solve(!ExprToASTConverter(expr))), {
      
        val sets = ExprToASTConverter.getSetTypes(expr)
        if (sets.size > 1)
          reporter.warning("Heterogeneous set types: " + sets.mkString(", "))
      
      })._1
    } catch {
      case ConversionException(badExpr, msg) =>
        reporter.info(badExpr, msg)
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
    reporter.info("BAPA< formula to be verified:\n" + NormalForms.nnf(!formula).toString)

    val z3 = new Context(formula, reporter)
    val startTime = System.nanoTime
    try {
      // Term rewriting and NNF/DNF transformation
      for (conjunction <- NormalForms(formula)) {
        z3.push
        try {
          // Guess orderings, create equivalence classes
          // for each ordering and solve the resulting formulas.
          GuessOrdering(EquiClassPartition.apply)(z3, conjunction)
        } catch {
          case UnsatException(_) =>
        }
        z3.pop
      }
      // No conjunction and no guessed ordering is satisfiable.
      // Return UNSAT
      false
    } catch {
      // Found a model (counter-example)
      case SatException(Model(ints, sets)) =>
        reporter.info("Counter-example found :")
        for ((name, value) <- ints)
          reporter.info("\t\t " + name + " -> " + value)
        for ((name, value) <- sets) 
          reporter.info("\t\t " + name + " -> " + value)
        // Return SAT
        true
    } finally {
      z3.delete
      val totalTime = ((System.nanoTime - startTime) / 1000000) / 1000.0
      reporter.info("Total time : " + totalTime)
    }
  }
}

// Thrown when a model was found after guessing
case class SatException(model: Model) extends Exception("A model was found")

// Thrown when a contradiction was derived during guessing
case class UnsatException(msg: String) extends Exception(msg)

// Convert PureScala expressions to OrdBAPA AST's
object ExprToASTConverter {
  import purescala.TypeTrees._
  import purescala.Trees._
  import Primitives._

  case class ConversionException(expr: Expr, msg: String) extends RuntimeException(msg)

  private def isSetType(_type: TypeTree) = _type match {
    case SetType(_) => true
    case _ => false
  }

  private def toSetTerm(expr: Expr): AST.Term = expr match {
    case Variable(id) if isSetType(id.getType) => Symbol(id.name, Symbol.SetType)
    case EmptySet(_) => AST.emptyset
    case FiniteSet(elems) if elems forall {_.getType == Int32Type} => AST.Op(UNION, (elems map toIntTerm map {_.singleton}).toList)
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
    case SetMin(set) if set.getType == SetType(Int32Type) => toSetTerm(set).inf
    case SetMax(set) if set.getType == SetType(Int32Type) => toSetTerm(set).sup
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

  def getSetTypes(expr: Expr): Set[TypeTree] = expr match {
    case Or(es) => (es map getSetTypes) reduceLeft (_ ++ _)
    case And(es) => (es map getSetTypes) reduceLeft (_ ++ _)
    case Not(e) => getSetTypes(e)
    case Implies(e1, e2) => getSetTypes(e1) ++ getSetTypes(e2)
    // Set formulas
    case ElementOfSet(_, set) => Set(set.getType, SetType(Int32Type))
    case SetEquals(set1, set2) => Set(set1.getType, set2.getType)
    case IsEmptySet(set) => Set(set.getType)
    case SubsetOf(set1, set2) => Set(set1.getType, set2.getType)
    // Integer formulas
    case LessThan(lhs, rhs) => getSetTypes(lhs) ++ getSetTypes(rhs)
    case LessEquals(lhs, rhs) => getSetTypes(lhs) ++ getSetTypes(rhs)
    case GreaterThan(lhs, rhs) => getSetTypes(lhs) ++ getSetTypes(rhs)
    case GreaterEquals(lhs, rhs) => getSetTypes(lhs) ++ getSetTypes(rhs)
    case Equals(lhs, rhs) => getSetTypes(lhs) ++ getSetTypes(rhs)
    // Integer terms
    case Plus(lhs, rhs) => getSetTypes(lhs) ++ getSetTypes(rhs)
    case Minus(lhs, rhs) => getSetTypes(lhs) ++ getSetTypes(rhs)
    case Times(lhs, rhs) => getSetTypes(lhs) ++ getSetTypes(rhs)
    case UMinus(e) => getSetTypes(e)
    case SetCardinality(set) => Set(set.getType)
    case SetMin(set) => Set(set.getType, SetType(Int32Type))
    case SetMax(set) => Set(set.getType, SetType(Int32Type))
    case _ => Set.empty[TypeTree]
  }

  def apply(expr: Expr) = toFormula(expr)
}