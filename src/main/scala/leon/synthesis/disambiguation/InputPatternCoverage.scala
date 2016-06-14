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

/**
 * @author Mikael
 * If possible, synthesizes a set of inputs for the function so that they cover all parts of the function.
 * Requires the function to only have pattern matchings without conditions, functions with single variable calls.
 * 
 * @param fds The set of functions to cover
 * @param fd The calling function
 */
class InputPatternCoverage(fd: TypedFunDef)(implicit c: LeonContext, p: Program) {

  def result(): Stream[Seq[Expr]] = coverFunDef(fd, Covered(Set(), Set()), None)

  private case class Covered(alreadyCovered: Set[TypedFunDef], alreadyCoveredLambdas: Set[Lambda]) {
    def apply(t: TypedFunDef) = alreadyCovered(t)
    def apply(l: Lambda) = alreadyCoveredLambdas(l)
    def +(t: TypedFunDef) = this.copy(alreadyCovered = alreadyCovered + t)
    def +(l: Lambda) = this.copy(alreadyCoveredLambdas = alreadyCoveredLambdas + l)
  }
  
  private def coverFunLike(paramIds: Seq[Identifier], body: Expr, args: Option[Seq[Expr]], covered: Covered): Stream[Seq[Expr]] = {
    val mapping = coverExpr(paramIds, body, covered, args.map(args => paramIds.zip(args).toMap).getOrElse(Map.empty))
    leon.utils.StreamUtils.cartesianMap(mapping) map { mapping =>
     paramIds.map(i => convert(List(i))(mapping).getOrElse(a(i.getType)))
    }
  }
  
  private def coverFunDef(f: TypedFunDef, covered: Covered, args: Option[Seq[Expr]]): Stream[Seq[Expr]] = if(covered(f)) {
    Stream(f.paramIds.map(x => a(x.getType)))
  } else {
    f.body match {
      case Some(body) => coverFunLike(f.paramIds, body, args, covered + f)
      case None => throw new InputPatternCoverageException(s"empty body for function $f")
    }
  }

  private def coverLambda(l: Lambda, covered: Covered, args: Option[Seq[Expr]]): Stream[Seq[Expr]] = if(covered(l)) {
    Stream(l.args.map(x => a(x.getType)))
  } else {
    coverFunLike(l.args.map(_.id), l.body, args, covered + l)
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
  
  def compose(oldBindings: Map[Identifier, Expr], newBindings: Seq[Expr]): Seq[Expr] = {
    newBindings.map { case Variable(id) => oldBindings.getOrElse(id, Variable(id)) case  e => e }
  }
  
  /** Map of g.left.symbol to the stream of expressions it could be assigned to */
  private def coverExpr(inputs: Seq[Identifier], e: Expr, covered: Covered, bindings: Map[Identifier, Expr]): Map[List[Identifier], Stream[Expr]] = {
    val res : Map[List[Identifier], Stream[Expr]] = 
    e match {
    case IfExpr(cond, thenn, elze) => throw new Exception("Requires only match/case pattern, got "+e)
    case MatchExpr(Variable(i), cases) if inputs.headOption == Some(i) =>
      val inputType = i.getType
      val coveringExprs = cases.map(coverMatchCase(inputType, _, covered, bindings))
      val interleaved = leon.utils.StreamUtils.interleave[Expr](coveringExprs)
      Map(List(i) -> interleaved)
    case FunctionInvocation(tfd@TypedFunDef(fd, targs), args @ (Reconstructor(ids)+:tail)) =>
      Map(ids -> coverFunDef(tfd, covered, Some(compose(bindings, args))).map(_.head))
      
    case Reconstructor(ids) =>
      Map(ids -> Stream(a(ids.last.getType)))
      
    case Application(Variable(f), args @ (Reconstructor(ids)+:tail)) =>
      bindings.get(f) match {
        case Some(l@Lambda(Seq(ValDef(i)), body))=>
          Map(ids -> coverLambda(l, covered, Some(compose(bindings, args))).map(_.head))
        case e => throw new InputPatternCoverageException("Wrong callback, expected lambda, got  " + e + " (bindings = " + bindings + ")"  )
      }
    case Operator(lhsrhs, builder) =>
      if(lhsrhs.length == 0) {
        Map()
      } else {
        lhsrhs.map(child => coverExpr(inputs, child, covered, bindings)).reduce(mergeCoverage)
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
  
  private def coverMatchCase(inputType: TypeTree, m: MatchCase, covered: Covered, bindings: Map[Identifier, Expr]) = m match {
    case MatchCase(pattern, guard, rhs) =>
      val variables = pattern.binders.toSeq
      val binders = coverExpr(variables, rhs, covered, bindings)
      val cartesian = leon.utils.StreamUtils.cartesianMap(binders)
      cartesian.map(binders => coverPattern(pattern, inputType, binders, covered))
  }
}