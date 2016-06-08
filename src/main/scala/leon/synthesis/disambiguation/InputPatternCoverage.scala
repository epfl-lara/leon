package leon
package synthesis.disambiguation

import purescala.Expressions._
import purescala.ExprOps
import purescala.Constructors._
import purescala.Extractors._
import purescala.Types._
import purescala.Common._
import purescala.Definitions.{FunDef, Program, TypedFunDef, ValDef}
import purescala.DefOps
import scala.collection.mutable.ListBuffer
import leon.LeonContext
import leon.purescala.Definitions.TypedFunDef
import leon.verification.VerificationContext
import leon.verification.VerificationPhase
import leon.solvers._
import scala.concurrent.duration._
import leon.verification.VCStatus
import leon.verification.VCResult
import leon.evaluators.AbstractEvaluator
import java.util.IdentityHashMap
import leon.utils.Position
import scala.collection.JavaConversions._
import leon.evaluators.DefaultEvaluator
import leon.grammars.ValueGrammar
import leon.datagen.GrammarDataGen

case class PatternNotSupportedException(p: Pattern) extends
  Exception(s"The pattern $p is not supported for coverage.")

/**
 * @author Mikael
 * If possible, synthesizes a set of inputs for the function so that they cover all parts of the function.
 * Requires the function to only have pattern matchings without conditions, functions with single variable calls.
 * 
 * @param fds The set of functions to cover
 * @param fd The calling function
 */
class InputPatternCoverage(fd: TypedFunDef)(implicit c: LeonContext, p: Program) {

  def result(): Stream[Seq[Expr]] = coverFunDef(fd, Covered(Set()))

  private case class Covered(alreadyCovered: Set[TypedFunDef]) {
    def apply(t: TypedFunDef) = alreadyCovered(t)
    def +(t: TypedFunDef) = this.copy(alreadyCovered + t)
  }
  
  
  private def coverFunDef(f: TypedFunDef, covered: Covered): Stream[Seq[Expr]] = if(covered(f)) {
    Stream(f.paramIds.map(x => a(x.getType)))
  } else {
    f.body match {
      case Some(body) =>
        val mapping = coverExpr(f.paramIds, body, covered + f)
        leon.utils.StreamUtils.cartesianMap(mapping) map { mapping =>
          f.paramIds.map(i => mapping.getOrElse(i, a(i.getType)))
        }
      case None => throw new Exception("empty body")
    }
  }
  
  private def mergeCoverage(a: Map[Identifier, Stream[Expr]], b: Map[Identifier, Stream[Expr]]):
    Map[Identifier, Stream[Expr]] = {
    if((a.keys.toSet intersect b.keys.toSet).nonEmpty)
      throw new Exception("Variable used twice: " + (a.keys.toSet intersect b.keys.toSet))
    a ++ b
  }
  
  object Reconstructor {
    def unapply(e: Expr): Option[(Identifier, Expr => Expr)] = e match {
      case Variable(id) => Some((id, e => e))
      case CaseClassSelector(cct, Reconstructor(id, f), ccid) if cct.fields.length == 1 =>
        Some((id, e => CaseClass(cct, Seq(f(e)))))
      case _ => None
    }
  }
    
  private def coverExpr(inputs: Seq[Identifier], e: Expr, covered: Covered): Map[Identifier, Stream[Expr]] = {
    e match {
    case IfExpr(cond, thenn, elze) => throw new Exception("Requires only match/case pattern, got "+e)
    case MatchExpr(Variable(i), cases) if inputs.headOption == Some(i) =>
      val inputType = i.getType
      val coveringExprs = cases.map(coverMatchCase(inputType, _, covered))
      val interleaved = leon.utils.StreamUtils.interleave[Expr](coveringExprs)
      Map(i -> interleaved)
    case FunctionInvocation(tfd@TypedFunDef(fd, targs), Reconstructor(id, builder)+:tail) =>
      Map(id -> coverFunDef(tfd, covered).map(_.head).map(builder))

    case Operator(lhsrhs, builder) =>
      if(lhsrhs.length == 0) {
        Map()
      } else {
        lhsrhs.map(child => coverExpr(inputs, child, covered)).reduce(mergeCoverage)
      }
  }
}
  
  /** Returns an instance of the given type. Make sure maps, lists, sets and bags have at least two elements.*/
  private def a(t: TypeTree): Expr = {
    t match {
      case MapType(keyType, valueType) =>
        val pairs = all(keyType).take(2).toSeq.zip(all(valueType).take(2).toSeq).toMap
        FiniteMap(pairs, keyType, valueType)
      case SetType(elemType) =>
        val elems = all(elemType).take(2).toSet
        FiniteSet(elems, elemType)
      case BagType(elemType) =>
        val elems = all(elemType).take(2).toSeq
        FiniteBag(elems.zip(1 to 2 map (IntLiteral)).toMap, elemType)
      case _ => all(t).head
    }
  }
  
  /** Returns all instance of the given type */
  private def all(t: TypeTree): Stream[Expr] = {
    val i = FreshIdentifier("i", t)
    val datagen = new GrammarDataGen(new DefaultEvaluator(c, p), ValueGrammar)
    val enumerated_inputs = datagen.generateMapping(Seq(i), BooleanLiteral(true), 10, 10).toStream
    enumerated_inputs.toStream.map(_.head._2)
  }
  
  // TODO: Take other constraints into account: Missed previous patterns ?
  private def coverPattern(p: Pattern, inputType: TypeTree, binders: Map[Identifier, Expr], covered: Covered): Expr = p match {
    case CaseClassPattern(binder, ct, subs) =>
      if(subs.exists{ case e: WildcardPattern => false case _ => true }) {
        throw PatternNotSupportedException(p)
      }
      val args = subs.collect { case e: WildcardPattern => e }
      CaseClass(ct, args.zipWithIndex.map{
        case (WildcardPattern(Some(o)), i) if binders contains o => binders(o)
        case (WildcardPattern(_), i) => a(ct.fieldsTypes(i))
      })
    case TuplePattern(binder, subs) =>
      if(subs.exists{ case e: WildcardPattern => false case _ => true }) {
        throw PatternNotSupportedException(p)
      }
      val args = subs.collect { case e: WildcardPattern => e }
      Tuple(args.zipWithIndex.map{
        case (WildcardPattern(Some(o)), i) if binders contains o => binders(o)
        case (WildcardPattern(_), i) => 
          inputType match {
            case TupleType(targs) =>
              a(targs(i))
            case _ => throw PatternNotSupportedException(p)
          }
      })
    case InstanceOfPattern(binder, ct) =>
      binder.map(b => binders.getOrElse(b, a(ct))).getOrElse(a(ct))
    case LiteralPattern(ob, value) => value
    case WildcardPattern(ob) => a(inputType)
    case _ => throw PatternNotSupportedException(p)
  }
  
  private def coverMatchCase(inputType: TypeTree, m: MatchCase, covered: Covered) = m match {
    case MatchCase(pattern, guard, rhs) =>
      val variables = pattern.binders.toSeq
      val binders = coverExpr(variables, rhs, covered)
      val cartesian = leon.utils.StreamUtils.cartesianMap(binders)
      cartesian.map(binders => coverPattern(pattern, inputType, binders, covered))
  }
}