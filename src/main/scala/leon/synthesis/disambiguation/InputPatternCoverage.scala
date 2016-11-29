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
import scala.language.implicitConversions

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

  type PathSegment = Either[Identifier, Int]
  case class Path(orig: Identifier, route: List[PathSegment]) {
    def :+(i: Identifier) = Path(orig, route :+ Left(i))
    def :+(i: Int) = Path(orig, route :+ Right(i))
   
    def getType: TypeTree = {
       (orig.getType /: route) {
        case (TupleType(targs), Right(index)) => targs(index - 1)
        case (cct@CaseClassType(ccd, targs), Left(id)) => cct.fieldsTypes(ccd.selectorID2Index(id))
        case e => throw new InputPatternCoverageException("Could not get type of path " + this + " because inconsistency " + e)
      }
    }
  }
  implicit def idToPath(i: Identifier): Path = Path(i, Nil)
  
  private case class Covered(alreadyCovered: Set[TypedFunDef], alreadyCoveredLambdas: Set[Lambda]) {
    def apply(t: TypedFunDef) = alreadyCovered(t)
    def apply(l: Lambda) = alreadyCoveredLambdas(l)
    def +(t: TypedFunDef) = this.copy(alreadyCovered = alreadyCovered + t)
    def +(l: Lambda) = this.copy(alreadyCoveredLambdas = alreadyCoveredLambdas + l)
  }
  
  private def argsToMap(paramIds: Seq[Identifier], args: Option[Seq[Expr]]) = 
    args.map(args => paramIds.zip(args).toMap).getOrElse(Map.empty)
  
  private def coverFunLike(paramIds: Seq[Identifier], body: Expr, args: Option[Seq[Expr]], covered: Covered): Stream[Seq[Expr]] = {
    val mapping = coverExpr(paramIds, body, covered, argsToMap(paramIds, args))
    leon.utils.StreamUtils.cartesianMap(mapping) map { mapping =>
      paramIds.map(i => convert(i)(mapping).getOrElse(a(i.getType)))
    }
  }
  
  private def uniqueValueOf(m: Map[Path, Stream[Expr]], id: Identifier): Expr = {
    m.get(id) match {
      case None => throw new InputPatternCoverageException(s"Did not find $id in $m")
      case Some(s) => s.headOption.getOrElse(throw new InputPatternCoverageException(s"Empty value for $id in $m"))
    }
  }
  
  private def coverFunDef(f: TypedFunDef, covered: Covered, args: Option[Seq[Expr]]): Stream[Seq[Expr]] = if(covered(f)) {
    Stream(f.paramIds.map(x => a(x.getType)))
  } else {
    f.body match {
      case Some(body) => coverFunLike(f.paramIds, body, args, covered + f)
      case None => 
        if(f.fd == p.library.mapMkString.get) {
          args match {
            case Some(Seq(mp, sepk_v, sep_entry, fkey, fvalue)) =>
              mp.getType match {
                case MapType(keyType, valueType) =>
                  val key1 = FreshIdentifier("k1", keyType)
                  val key2 = FreshIdentifier("k2", keyType)
                  val value1 = FreshIdentifier("v1", valueType)
                  val value2 = FreshIdentifier("v2", valueType)
                  val dumbbody =
                    tupleWrap(Seq(application(fkey, Seq(Variable(key1))),
                                  application(fkey, Seq(Variable(key2))),
                                  Variable(f.paramIds(1)),
                                  Variable(f.paramIds(2)),
                                  application(fvalue, Seq(Variable(value1))),
                                  application(fvalue, Seq(Variable(value2)))))
                  val mapping = coverExpr(f.paramIds, dumbbody, covered + f, argsToMap(f.paramIds, args))
                  val key1v = uniqueValueOf(mapping, key1)
                  val key2v = uniqueValueOf(mapping, key2)
                  val key2vUnique = if(key1v == key2v) {
                    all(keyType).filter(e => e != key1v).headOption.getOrElse(key2v)
                  } else key2v
                  val value1v = uniqueValueOf(mapping, value1)
                  val value2v = uniqueValueOf(mapping, value2)
                  val remaining_mapping = mapping - key1 - key2 - value1 - value2
                  val firstValue = FiniteMap(Map(key1v -> value1v, key2vUnique -> value2v), keyType, valueType)
                  leon.utils.StreamUtils.cartesianMap(remaining_mapping) map { mapping =>
                     firstValue +:
                     f.paramIds.tail.map(i => convert(i)(mapping).getOrElse(a(i.getType)))
                  }
                case _ => throw new InputPatternCoverageException(s"Wrong usage of $f - no map type")
              }
            case _ => throw new InputPatternCoverageException(s"Wrong usage of $f")
          }
        }/* else if(f.fd == p.library.bagMkString.get) {
          
        } else if(f.fd == p.library.setMkString.get) {
          
        } */else throw new InputPatternCoverageException(s"empty body for function $f")
    }
  }

  private def coverLambda(l: Lambda, covered: Covered, args: Option[Seq[Expr]]): Stream[Seq[Expr]] = if(covered(l)) {
    Stream(l.args.map(x => a(x.getType)))
  } else {
    coverFunLike(l.args.map(_.id), l.body, args, covered + l)
  }
  
  private def mergeCoverage(a: Map[Path, Stream[Expr]], b: Map[Path, Stream[Expr]]):
    Map[Path, Stream[Expr]] = {
    if((a.keys.toSet intersect b.keys.toSet).nonEmpty)
      throw new InputPatternCoverageException("Variable used twice: " + (a.keys.toSet intersect b.keys.toSet)+"\n"+a+"\n"+b)
    a ++ b
  }
  
  object Reconstructor {
    def unapply(e: Expr): Option[Path] = e match {
      case Variable(id) => Some(id)
      case CaseClassSelector(cct, Reconstructor(path), ccid) =>
        Some(path :+ ccid)
      case TupleSelect(Reconstructor(path), index) =>
        Some(path :+ index)
      case _ => 
        None
    }
  }
  
  def compose(oldBindings: Map[Identifier, Expr], newBindings: Seq[Expr]): Seq[Expr] = {
    newBindings.map { case Variable(id) => oldBindings.getOrElse(id, Variable(id)) case  e => e }
  }
  
  /** Map of g.left.symbol to the stream of expressions it could be assigned to */
  private def coverExpr(inputs: Seq[Identifier], e: Expr, covered: Covered, bindings: Map[Identifier, Expr]): Map[Path, Stream[Expr]] = {
    //println(s"Covering expr (inputs = $inputs, bindings = $bindings): \n$e")
    val res : Map[Path, Stream[Expr]] = 
    e match {
    case IfExpr(Reconstructor(path), thenn, elze) => 
      mergeCoverage(
      mergeCoverage(
          Map(path -> Stream(BooleanLiteral(true), BooleanLiteral(false))),
          coverExpr(inputs, thenn, covered, bindings)
      ),
          coverExpr(inputs, elze, covered, bindings)
      )
      
    case IfExpr(cond, thenn, elze) => throw new InputPatternCoverageException("Requires only match/case pattern, got "+e)
    case MatchExpr(Reconstructor(path), cases) if inputs.nonEmpty && inputs.headOption == Some(path.orig) =>
      val pathType = path.getType
      val coveringExprs = cases.map(coverMatchCase(pathType, _, covered, bindings))
      val interleaved = leon.utils.StreamUtils.interleave[Expr](coveringExprs)
      Map(path -> interleaved)
    case FunctionInvocation(tfd@TypedFunDef(fd, targs), args @ (Reconstructor(path)+:tail)) =>
      Map(path -> coverFunDef(tfd, covered, Some(compose(bindings, args))).map(_.head))
      
    case Reconstructor(path) /*if inputs.nonEmpty && inputs.headOption == Some(path.orig)*/ =>
      Map(path -> Stream(a(path.getType)))
      
    case Application(Variable(f), args @ (Reconstructor(path)+:tail)) =>
      bindings.get(f) match {
        case Some(l@Lambda(Seq(ValDef(i)), body))=>
          Map(path -> coverLambda(l, covered, Some(compose(bindings, args))).map(_.head))
        case e => throw new InputPatternCoverageException("Wrong callback, expected lambda, got  " + e + " (bindings = " + bindings + ")"  )
      }
    case Operator(lhsrhs, builder) =>
      if(lhsrhs.length == 0) {
        Map()
      } else {
        lhsrhs.map(child => coverExpr(inputs, child, covered, bindings)).reduce(mergeCoverage)
      }
    }
    //println(s"covered $e and got $res")
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
  
  def convert(topLevel: Path)(implicit binders: Map[Path, Expr]): Option[Expr] = {
    binders.get(topLevel) match {
      case None =>
        topLevel.getType match {
        case cct@CaseClassType(ccd, targs) =>
          val args = ccd.fieldsIds.map(id =>
              (convert(topLevel :+ id) match { case Some(e) => e case None => return None }): Expr )
          Some(CaseClass(cct, args))
        case tt@TupleType(targs) =>
          val args = (1 to targs.length).map(index =>
            (convert(topLevel :+ index) match { case Some(e) => e case None => return None }): Expr )
          Some(Tuple(args.toSeq))
        case _ => None
      }
      case e => e
    }
  }
  
  // TODO: Take other constraints into account: Missed previous patterns ?
  private def coverPattern(p: Pattern, inputType: TypeTree, binders: Map[Path, Expr], covered: Covered): Expr = p match {
    case CaseClassPattern(binder, ct, subs) =>
      if(subs.exists{ case e: WildcardPattern => false case _ => true }) {
        throw PatternNotSupportedException(p)
      }
      val args = subs.collect { case e: WildcardPattern => e }
      CaseClass(ct, args.zipWithIndex.map{
        case (WildcardPattern(Some(o)), i) =>
          convert(o)(binders).getOrElse((throw PatternExtractionErrorException(p, s"Not able to recover value of ${o}")): Expr)
        case (WildcardPattern(_), i) => a(ct.fieldsTypes(i))
      })
    case TuplePattern(binder, subs) =>
      if(subs.exists{ case e: WildcardPattern => false case _ => true }) {
        throw PatternNotSupportedException(p)
      }
      val args = subs.collect { case e: WildcardPattern => e }
      Tuple(args.zipWithIndex.map{
        case (WildcardPattern(Some(o)), i) => convert(o)(binders).getOrElse((throw PatternNotSupportedException(p)): Expr)
        case (WildcardPattern(_), i) => 
          inputType match {
            case TupleType(targs) =>
              a(targs(i))
            case _ => throw PatternNotSupportedException(p)
          }
      })
    case InstanceOfPattern(binder, ct) =>
      binder.map(b => convert(b)(binders).getOrElse((throw PatternNotSupportedException(p)): Expr)).getOrElse(a(ct))
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