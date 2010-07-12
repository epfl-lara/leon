package orderedsets

import purescala.Reporter
import purescala.Extensions.Solver
import Reconstruction.Model

import RPrettyPrinter.rpp

class Main(reporter: Reporter) extends Solver(reporter) {
  import purescala.Trees.Expr
  import AST.Formula
  val description = "BAPA with ordering"
  override val shortDescription = "BAPA<"

  // checks for V-A-L-I-D-I-T-Y !
  // Some(true) means formula is valid (negation is unsat)
  // Some(false) means formula is not valid (negation is sat)
  // None means you don't know.
  //
  // If the formula was found to be not valid,
  // a counter-example is displayed (i.e. the model for negated formula)
  def solve(exprWithLets: Expr): Option[Boolean] = {
    //reporter.info("INPUT to Ordered BAPA\n" + rpp(exprWithLets))

    val expr = purescala.Trees.expandLets(exprWithLets)

    //reporter.info("INPUT to Ordered BAPA\n" + rpp(expr))

    //reporter.info("Sets: " + ExprToASTConverter.getSetTypes(expr))
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
      case IncompleteException(msg) =>
        reporter.info(msg)
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
  def solve(formula: Formula): Boolean = {
    //reporter.info("BAPA< formula to be shown unsat:\n" + NormalForms.nnf(formula).toString)

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
        if (!ExprToASTConverter.formulaRelaxed) true
        else throw (new IncompleteException("OrdBAPA: Relaxed formula was found satisfiable."))
    } finally {
      z3.delete
      val totalTime = ((System.nanoTime - startTime) / 1000000) / 1000.0
      //reporter.info("BAPA< total time : " + totalTime)
    }
  }
}

// Thrown when a model was found after guessing
case class SatException(model: Model) extends Exception("A model was found")

// Thrown when a contradiction was derived during guessing
case class UnsatException(msg: String) extends Exception(msg)

case class ConversionException(expr: purescala.Trees.Expr, msg: String) extends RuntimeException(msg)


// Convert PureScala expressions to OrdBAPA AST's
object ExprToASTConverter {
  import purescala.TypeTrees._
  import purescala.Trees._
  import Primitives._

  var formulaRelaxed = false

  def isSetType(_type: TypeTree) = _type match {
    case SetType(_) => true
    case _ => false
  }

  def isAcceptableType(_type: TypeTree) = isSetType(_type) || _type == Int32Type

  def makeEq(v: Variable, t: Expr) = v.getType match {
    case Int32Type => Equals(v, t)
    case tpe if isSetType(tpe) => SetEquals(v, t)
    case _ => throw (new ConversionException(v, "is of type " + v.getType + " and cannot be handled by OrdBapa"))
  }

  private def toSetTerm(expr: Expr): AST.Term = expr match {
    case ResultVariable() if isSetType(expr.getType) => Symbol("#res", Symbol.SetType)
    case Variable(id) if isSetType(id.getType) => Symbol(id.uniqueName, Symbol.SetType)
    case EmptySet(_) => AST.emptyset
    case FiniteSet(elems) if elems forall {_.getType == Int32Type} => AST.Op(UNION, (elems map toIntTerm map {_.singleton}).toList)
    case SetCardinality(set) => toSetTerm(set).card
    case SetIntersection(set1, set2) => toSetTerm(set1) ** toSetTerm(set2)
    case SetUnion(set1, set2) => toSetTerm(set1) ++ toSetTerm(set2)
    case SetDifference(set1, set2) => toSetTerm(set1) -- toSetTerm(set2)
    case Variable(_) => throw ConversionException(expr, "is a variable of type " + expr.getType + " and cannot be converted to bapa< set variable")
    case _ => throw ConversionException(expr, "Cannot convert to bapa< set term")
  }

  private def toIntTerm(expr: Expr): AST.Term = expr match {
    case ResultVariable() if expr.getType == Int32Type => Symbol("#res", Symbol.IntType)
    case Variable(id) if id.getType == Int32Type => Symbol(id.uniqueName, Symbol.IntType)
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
    case Variable(id) if id.getType == BooleanType => Symbol(id.uniqueName, Symbol.BoolType)
    case Or(exprs) => AST.Or((exprs map toFormula).toList)
    case And(exprs) => AST.And((exprs map toFormula).toList)
    case Not(expr) => !toFormula(expr)
    case Implies(expr1, expr2) => !(toFormula(expr1)) || toFormula(expr2)

    // Set Formulas
    case ElementOfSet(elem, set) => toIntTerm(elem) selem toSetTerm(set)
    case SetEquals(set1, set2) => toSetTerm(set1) seq toSetTerm(set2)
    // case IsEmptySet(set) => toSetTerm(set).card === 0
    case SubsetOf(set1, set2) => toSetTerm(set1) subseteq toSetTerm(set2)

    // Integer Formulas
    case LessThan(lhs, rhs) => toIntTerm(lhs) < toIntTerm(rhs)
    case LessEquals(lhs, rhs) => toIntTerm(lhs) <= toIntTerm(rhs)
    case GreaterThan(lhs, rhs) => toIntTerm(lhs) > toIntTerm(rhs)
    case GreaterEquals(lhs, rhs) => toIntTerm(lhs) >= toIntTerm(rhs)
    case Equals(lhs, rhs) if lhs.getType == Int32Type && rhs.getType == Int32Type => toIntTerm(lhs) === toIntTerm(rhs)

    // Assuming the formula to be True
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
    // case IsEmptySet(set) => Set(set.getType)
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

  def apply(expr: Expr) = {
    formulaRelaxed = false;
    expr match {
      case And(exprs) => AST.And((exprs map toRelaxedFormula).toList)
      case _ => toRelaxedFormula(expr)
    }
  }

  private def toRelaxedFormula(expr: Expr): AST.Formula =
    try {
      toFormula(expr)
    } catch {
      case ConversionException(_, _) =>
        formulaRelaxed = true
        // Assuming the formula to be True
        AST.True
    }
}
