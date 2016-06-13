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
import leon.purescala.Definitions._
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

class InputPatternCoverageException(msg: String) extends
  Exception(msg)

case class PatternNotSupportedException(p: Pattern) extends
  InputPatternCoverageException(s"The pattern $p is not supported for coverage.")

case class PatternExtractionErrorException(p: Pattern, msg: String) extends
  InputPatternCoverageException(s"The pattern $p cause problem during extraction: "+msg)

case class FunDefNotCoverableException(fd: FunDef, bindings: Map[_, _]) extends
  InputPatternCoverageException(s"The function is not supported for coverage:\n$fd\n under bindings $bindings")

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
          f.paramIds.map(i => convert(List(i))(mapping).getOrElse(a(i.getType)))
        }
      case None => throw new Exception("empty body")
    }
  }
  
  private def mergeCoverage(a: Map[List[Identifier], Stream[Expr]], b: Map[List[Identifier], Stream[Expr]]):
    Map[List[Identifier], Stream[Expr]] = {
    if((a.keys.toSet intersect b.keys.toSet).nonEmpty)
      throw new Exception("Variable used twice: " + (a.keys.toSet intersect b.keys.toSet))
    a ++ b
  }
  
  object Reconstructor {
    def unapply(e: Expr): Option[List[Identifier]] = e match {
      case Variable(id) => Some(List(id))
      case CaseClassSelector(cct, Reconstructor(ids), ccid) =>
        Some(ids :+ ccid)
      case _ => 
        None
    }
  }
  
  /** Map of g.left.symbol to the stream of expressions it could be assigned to */
  private def coverExpr(inputs: Seq[Identifier], e: Expr, covered: Covered): Map[List[Identifier], Stream[Expr]] = {
    val res : Map[List[Identifier], Stream[Expr]] = 
    e match {
    case IfExpr(cond, thenn, elze) => throw new Exception("Requires only match/case pattern, got "+e)
    case MatchExpr(Variable(i), cases) if inputs.headOption == Some(i) =>
      val inputType = i.getType
      val coveringExprs = cases.map(coverMatchCase(inputType, _, covered))
      val interleaved = leon.utils.StreamUtils.interleave[Expr](coveringExprs)
      Map(List(i) -> interleaved)
    case FunctionInvocation(tfd@TypedFunDef(fd, targs), Reconstructor(ids)+:tail) =>
      Map(ids -> coverFunDef(tfd, covered).map(_.head))
      
    case Application(Variable(f), Reconstructor(ids)+:tail) =>
      val typicalArgValue = f.getType match {
        case FunctionType(in+:typeTails, out) => a(in)
        case e=> throw new InputPatternCoverageException("Wrong type, expected A => B, got  " + e)
      }
      Map(ids -> Stream(typicalArgValue))

    case Operator(lhsrhs, builder) =>
      if(lhsrhs.length == 0) {
        Map()
      } else {
        lhsrhs.map(child => coverExpr(inputs, child, covered)).reduce(mergeCoverage)
      }
    }
    res
  }
  
  /** Returns an instance of the given type. Makes sure maps, sets and bags have at least two elements.*/
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
  
  def convert(topLevel: List[Identifier])(implicit binders: Map[List[Identifier], Expr]): Option[Expr] = {
    binders.get(topLevel) match {
      case None =>
      topLevel.last.getType match {
        case cct@CaseClassType(ccd, targs) =>
          val args = ccd.fieldsIds.map(id =>
              (convert(topLevel :+ id) match { case Some(e) => e case None => return None }): Expr )
          return Some(CaseClass(cct, args))
        case _ => return None
      }
      case e => e
    }
  }
  
  // TODO: Take other constraints into account: Missed previous patterns ?
  private def coverPattern(p: Pattern, inputType: TypeTree, binders: Map[List[Identifier], Expr], covered: Covered): Expr = p match {
    case CaseClassPattern(binder, ct, subs) =>
      if(subs.exists{ case e: WildcardPattern => false case _ => true }) {
        throw PatternNotSupportedException(p)
      }
      val args = subs.collect { case e: WildcardPattern => e }
      CaseClass(ct, args.zipWithIndex.map{
        case (WildcardPattern(Some(o)), i) =>
          convert(List(o))(binders).getOrElse((throw PatternExtractionErrorException(p, s"Not able to recover value of ${o}")): Expr)
        case (WildcardPattern(_), i) => a(ct.fieldsTypes(i))
      })
    case TuplePattern(binder, subs) =>
      if(subs.exists{ case e: WildcardPattern => false case _ => true }) {
        throw PatternNotSupportedException(p)
      }
      val args = subs.collect { case e: WildcardPattern => e }
      Tuple(args.zipWithIndex.map{
        case (WildcardPattern(Some(o)), i) => convert(List(o))(binders).getOrElse((throw PatternNotSupportedException(p)): Expr)
        case (WildcardPattern(_), i) => 
          inputType match {
            case TupleType(targs) =>
              a(targs(i))
            case _ => throw PatternNotSupportedException(p)
          }
      })
    case InstanceOfPattern(binder, ct) =>
      binder.map(b => convert(List(b))(binders).getOrElse((throw PatternNotSupportedException(p)): Expr)).getOrElse(a(ct))
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