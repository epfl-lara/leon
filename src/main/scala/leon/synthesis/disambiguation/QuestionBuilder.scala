package leon
package synthesis.disambiguation

import synthesis.RuleClosed
import synthesis.Solution
import evaluators.DefaultEvaluator
import purescala.Expressions._
import purescala.ExprOps
import purescala.Constructors._
import purescala.Extractors._
import purescala.Types.TypeTree
import purescala.Common.Identifier
import purescala.Definitions.Program
import purescala.DefOps
import grammars.ValueGrammar
import bonsai.enumerators.MemoizedEnumerator
import solvers.Model
import solvers.ModelBuilder
import scala.collection.mutable.ListBuffer

object QuestionBuilder {
  /** Sort methods for questions. You can build your own */
  trait QuestionSortingType {
    def apply[T <: Expr](e: Question[T]): Int
  }
  object QuestionSortingType {
    case object IncreasingInputSize extends QuestionSortingType {
      def apply[T <: Expr](q: Question[T]) = q.inputs.map(i => ExprOps.count(e => 1)(i)).sum
    }
    case object DecreasingInputSize extends QuestionSortingType{
      def apply[T <: Expr](q: Question[T]) = -IncreasingInputSize(q)
    }
  }
  // Add more if needed.
  
  /** Sort methods for question's answers. You can (and should) build your own. */
  abstract class AlternativeSortingType[T <: Expr] extends Ordering[T] { self =>
    /** Prioritizes this comparison operator against the second one. */
    def &&(other: AlternativeSortingType[T]): AlternativeSortingType[T] = new AlternativeSortingType[T] {
      def compare(e: T, f: T): Int = {
        val ce = self.compare(e, f)
        if(ce == 0) other.compare(e, f) else ce
      }
    }
  }
  object AlternativeSortingType {
    /** Presents shortest alternatives first */
    case class ShorterIsBetter[T <: Expr]()(implicit c: LeonContext) extends AlternativeSortingType[T] {
      def compare(e: T, f: T) = e.asString.length - f.asString.length
    }
    /** Presents balanced alternatives first */
    case class BalancedParenthesisIsBetter[T <: Expr]()(implicit c: LeonContext) extends AlternativeSortingType[T] {
      def convert(e: T): Int = {
        val s = e.asString
        var openP, openB, openC = 0
        for(c <- s) c match {
          case '(' if openP >= 0 => openP += 1
          case ')'               => openP -= 1
          case '{' if openB >= 0 => openB += 1
          case '}'               => openB -= 1
          case '[' if openC >= 0 => openC += 1
          case ']'               => openC -= 1
          case _ =>
        }
        Math.abs(openP) + Math.abs(openB) + Math.abs(openC)
      }
      def compare(e: T, f: T): Int = convert(e) - convert(f) 
    }
  }
}

/**
 * Builds a set of disambiguating questions for the problem
 * 
 * {{{
 * def f(input: input.getType): T =
 *   [element of r.solution]
 * }}}
 * 
 * @tparam T A subtype of Expr that will be the type used in the Question[T] results.
 * @param input The identifier of the unique function's input. Must be typed or the type should be defined by setArgumentType
 * @param ruleApplication The set of solutions for the body of f
 * @param filter A function filtering which outputs should be considered for comparison.
 * @return An ordered
 * 
 */
class QuestionBuilder[T <: Expr](input: Seq[Identifier], solutions: Stream[Solution], filter: Expr => Option[T])(implicit c: LeonContext, p: Program) {
  import QuestionBuilder._
  private var _argTypes = input.map(_.getType)
  private var _questionSorMethod: QuestionSortingType = QuestionSortingType.IncreasingInputSize
  private var _alternativeSortMethod: AlternativeSortingType[T] = AlternativeSortingType.BalancedParenthesisIsBetter[T]() && AlternativeSortingType.ShorterIsBetter[T]() 
  private var solutionsToTake = 30
  private var expressionsToTake = 30
  private var keepEmptyAlternativeQuestions: T => Boolean = Set()

  /** Sets the way to sort questions. See [[QuestionSortingType]] */
  def setSortQuestionBy(questionSorMethod: QuestionSortingType) = { _questionSorMethod = questionSorMethod; this }
  /** Sets the way to sort alternatives. See [[AlternativeSortingType]] */
  def setSortAlternativesBy(alternativeSortMethod: AlternativeSortingType[T]) = { _alternativeSortMethod = alternativeSortMethod; this }
  /** Sets the argument type. Not needed if the input identifier is already assigned a type. */
  def setArgumentType(argTypes: List[TypeTree]) = { _argTypes = argTypes; this }
  /** Sets the number of solutions to consider. Default is 15 */
  def setSolutionsToTake(n: Int) = { solutionsToTake = n; this }
  /** Sets the number of expressions to consider. Default is 15 */
  def setExpressionsToTake(n: Int) = { expressionsToTake = n; this }
  /** Sets if when there is no alternative, the question should be kept. */
  def setKeepEmptyAlternativeQuestions(b: T => Boolean) = {keepEmptyAlternativeQuestions = b; this }
  
  private def run(s: Solution, elems: Seq[(Identifier, Expr)]): Option[Expr] = {
    val newProgram = DefOps.addFunDefs(p, s.defs, p.definedFunctions.head)
    val e = new DefaultEvaluator(c, newProgram)
    val model = new ModelBuilder
    model ++= elems
    val modelResult = model.result()
    e.eval(s.term, modelResult).result
  }
  
  /** Returns a list of input/output questions to ask to the user. */
  def result(): List[Question[T]] = {
    if(solutions.isEmpty) return Nil
    
    val enum = new MemoizedEnumerator[TypeTree, Expr](ValueGrammar.getProductions)
    val values = enum.iterator(tupleTypeWrap(_argTypes))
    val instantiations = values.map {
      v => input.zip(unwrapTuple(v, input.size))
    }
    
    val enumerated_inputs = instantiations.take(expressionsToTake).toList
    
    val solution = solutions.head
    val alternatives = solutions.drop(1).take(solutionsToTake).toList
    val questions = ListBuffer[Question[T]]()
    for{possible_input             <- enumerated_inputs
        current_output_nonfiltered <- run(solution, possible_input)
        current_output             <- filter(current_output_nonfiltered)} {
      val alternative_outputs = (
        for{alternative                 <- alternatives
            alternative_output          <- run(alternative, possible_input)
            alternative_output_filtered <- filter(alternative_output)
            if alternative_output != current_output
      } yield alternative_output_filtered).distinct
      if(alternative_outputs.nonEmpty || keepEmptyAlternativeQuestions(current_output)) {
        questions += Question(possible_input.map(_._2), current_output, alternative_outputs.sortWith((e,f) => _alternativeSortMethod.compare(e, f) <= 0))
      }
    }
    questions.toList.sortBy(_questionSorMethod(_))
  }
}