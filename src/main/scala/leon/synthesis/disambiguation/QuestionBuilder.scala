/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis.disambiguation

import datagen.GrammarDataGen
import synthesis.Solution
import evaluators.DefaultEvaluator
import purescala.Expressions._
import purescala.ExprOps
import purescala.Types.{StringType, TypeTree}
import purescala.Common.Identifier
import purescala.Definitions.Program
import purescala.DefOps
import grammars._
import solvers.ModelBuilder
import scala.collection.mutable.ListBuffer
import evaluators.AbstractEvaluator
import scala.annotation.tailrec

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
  
  /** Specific enumeration of strings, which can be used with the QuestionBuilder#setValueEnumerator method */
  object SpecialStringValueGrammar extends SimpleExpressionGrammar {
    def computeProductions(t: TypeTree)(implicit ctx: LeonContext): Seq[Prod] = t match {
      case StringType =>
        List(
          terminal(StringLiteral("")),
          terminal(StringLiteral("a")),
          terminal(StringLiteral("\"'\n\t")),
          terminal(StringLiteral("Lara 2007"))
        )
      case _ => ValueGrammar.computeProductions(t)
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
 * @param filter A function filtering which outputs should be considered for comparison.
 *               It takes as input the sequence of outputs already considered for comparison, and the new output.
 *               It should return Some(result) if the result can be shown, and None else.
 * 
 */
class QuestionBuilder[T <: Expr](
    input: Seq[Identifier],
    solutions: Stream[Solution],
    filter: (Seq[T], Expr) => Option[T])(implicit c: LeonContext, p: Program) {
  import QuestionBuilder._
  private var _argTypes = input.map(_.getType)
  private var _questionSorMethod: QuestionSortingType = QuestionSortingType.IncreasingInputSize
  private var _alternativeSortMethod: AlternativeSortingType[T] = AlternativeSortingType.BalancedParenthesisIsBetter[T]() && AlternativeSortingType.ShorterIsBetter[T]() 
  private var solutionsToTake = 30
  private var expressionsToTake = 30
  private var keepEmptyAlternativeQuestions: T => Boolean = Set()
  private var value_enumerator: ExpressionGrammar = ValueGrammar

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
  /** Sets the way to enumerate expressions */
  def setValueEnumerator(v: ExpressionGrammar) = value_enumerator = v
  
  private def run(s: Solution, elems: Seq[(Identifier, Expr)]): Option[Expr] = {
    val newProgram = DefOps.addFunDefs(p, s.defs, p.definedFunctions.head)
    val e = new AbstractEvaluator(c, newProgram)
    val model = new ModelBuilder
    model ++= elems
    val modelResult = model.result()
    for{x <- e.eval(s.term, modelResult).result
        res = x._1
        simp = ExprOps.simplifyArithmetic(res)}
      yield simp
  }
  
  /** Make all generic values unique.
    * Duplicate generic values are not suitable for disambiguating questions since they remove an order. */
  def makeGenericValuesUnique(a: Expr): Expr = {
    var genVals = Set[Expr with Terminal]()
    def freshenValue(g: Expr with Terminal): Option[Expr with Terminal] = g match {
      case g: GenericValue => Some(GenericValue(g.tp, g.id + 1))
      case StringLiteral(s) =>
        val i = s.lastIndexWhere { c => c < '0' || c > '9' }
        val prefix = s.take(i+1)
        val suffix = s.drop(i+1)
        Some(StringLiteral(prefix + (if(suffix == "") "0" else (suffix.toInt + 1).toString)))
      case InfiniteIntegerLiteral(i) => Some(InfiniteIntegerLiteral(i+1))
      case IntLiteral(i) => if(i == Integer.MAX_VALUE) None else Some(IntLiteral(i+1))
      case CharLiteral(c) => if(c == Char.MaxValue) None else Some(CharLiteral((c+1).toChar))
      case otherLiteral => None
    }
    @tailrec @inline def freshValue(g: Expr with Terminal): Expr with Terminal = {
          if(genVals contains g)
            freshenValue(g) match {
              case None => g
              case Some(v) => freshValue(v)
            }
          else {
            genVals += g
            g
          }
    }
    ExprOps.postMap{ e => e match {
      case g:Expr with Terminal =>
        Some(freshValue(g))
      case _ => None
    }}(a)
  }
  
  /** Returns a list of input/output questions to ask to the user. */
  def result(): List[Question[T]] = {
    if(solutions.isEmpty) return Nil

    val datagen = new GrammarDataGen(new DefaultEvaluator(c, p), value_enumerator)
    val enumerated_inputs = datagen.generateMapping(input, BooleanLiteral(true), expressionsToTake, expressionsToTake)
    .map(inputs =>
      inputs.map(id_expr =>
        (id_expr._1, makeGenericValuesUnique(id_expr._2)))).toList

    val solution = solutions.head
    val alternatives = solutions.drop(1).take(solutionsToTake).toList
    val questions = ListBuffer[Question[T]]()
    for {
      possibleInput            <- enumerated_inputs
      currentOutputNonFiltered <- run(solution, possibleInput)
      currentOutput            <- filter(Seq(), currentOutputNonFiltered)
    } {
      
      val alternative_outputs = (ListBuffer[T](currentOutput) /: alternatives) { (prev, alternative) =>
        run(alternative, possibleInput) match {
          case Some(alternative_output) if alternative_output != currentOutput =>
            filter(prev, alternative_output) match {
              case Some(alternative_output_filtered) =>
                prev += alternative_output_filtered
              case _ => prev
            }
          case _ => prev
        }
      }.drop(1).toList.distinct
      if(alternative_outputs.nonEmpty || keepEmptyAlternativeQuestions(currentOutput)) {
        questions += Question(possibleInput.map(_._2), currentOutput, alternative_outputs.sortWith((e,f) => _alternativeSortMethod.compare(e, f) <= 0))
      }
    }
    questions.toList.sortBy(_questionSorMethod(_))
  }
}
