/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import Expressions._
import Common._
import Types._
import Constructors._

object Extractors {

  /** Operator Extractor to extract any Expression in a consistent way.
    *
    * You can match on any Leon Expr, and then get both a Seq[Expr] of
    * subterms and a builder fonction that takes a Seq of subterms (of same
    * length) and rebuild the original node.
    *
    * Those extractors do not perform any syntactic simplifications. They
    * rebuild the node using the case class (not the constructor, that performs
    * simplifications). The rational behind this decision is to have core
    * tools for performing tree transformations that are very predictable, if
    * one need to simplify the tree, it is easy to write/call a simplification
    * function that would simply apply the corresponding constructor for each node.
    */
  object Operator extends TreeExtractor[Expr] {
    def unapply(expr: Expr): Option[(Seq[Expr], (Seq[Expr]) => Expr)] = expr match {
      /* Unary operators */
      case Not(t) =>
        Some((Seq(t), (es: Seq[Expr]) => Not(es.head)))
      case Choose(expr) =>
        Some((Seq(expr), (es: Seq[Expr]) => Choose(es.head)))
      case UMinus(t) =>
        Some((Seq(t), (es: Seq[Expr]) => UMinus(es.head)))
      case BVUMinus(t) =>
        Some((Seq(t), (es: Seq[Expr]) => BVUMinus(es.head)))
      case RealUMinus(t) =>
        Some((Seq(t), (es: Seq[Expr]) => RealUMinus(es.head)))
      case BVNot(t) =>
        Some((Seq(t), (es: Seq[Expr]) => BVNot(es.head)))
      case StringLength(t) =>
        Some((Seq(t), (es: Seq[Expr]) => StringLength(es.head)))
      case StringBigLength(t) =>
        Some((Seq(t), (es: Seq[Expr]) => StringBigLength(es.head)))
      case Int32ToString(t) =>
        Some((Seq(t), (es: Seq[Expr]) => Int32ToString(es.head)))
      case BooleanToString(t) =>
        Some((Seq(t), (es: Seq[Expr]) => BooleanToString(es.head)))
      case IntegerToString(t) =>
        Some((Seq(t), (es: Seq[Expr]) => IntegerToString(es.head)))
      case CharToString(t) =>
        Some((Seq(t), (es: Seq[Expr]) => CharToString(es.head)))
      case RealToString(t) =>
        Some((Seq(t), (es: Seq[Expr]) => RealToString(es.head)))
      case SetCardinality(t) =>
        Some((Seq(t), (es: Seq[Expr]) => SetCardinality(es.head)))
      case CaseClassSelector(cd, e, sel) =>
        Some((Seq(e), (es: Seq[Expr]) => CaseClassSelector(cd, es.head, sel)))
      case IsInstanceOf(e, ct) =>
        Some((Seq(e), (es: Seq[Expr]) => IsInstanceOf(es.head, ct)))
      case AsInstanceOf(e, ct) =>
        Some((Seq(e), (es: Seq[Expr]) => AsInstanceOf(es.head, ct)))
      case TupleSelect(t, i) =>
        Some((Seq(t), (es: Seq[Expr]) => TupleSelect(es.head, i)))
      case ArrayLength(a) =>
        Some((Seq(a), (es: Seq[Expr]) => ArrayLength(es.head)))
      case Lambda(args, body) =>
        Some((Seq(body), (es: Seq[Expr]) => Lambda(args, es.head)))
      case FiniteLambda(mapping, dflt, tpe) =>
        val sze = tpe.from.size + 1
        val subArgs = mapping.flatMap { case (args, v) => args :+ v }
        val builder = (as: Seq[Expr]) => {
          def rec(kvs: Seq[Expr]): Seq[(Seq[Expr], Expr)] = kvs match {
            case seq if seq.size >= sze =>
              val (args :+ res, rest) = seq.splitAt(sze)
              (args -> res) +: rec(rest)
            case Seq() => Seq.empty
            case _ => sys.error("unexpected number of key/value expressions")
          }
          FiniteLambda(rec(as.init), as.last, tpe)
        }
        Some((subArgs :+ dflt, builder))
      case Forall(args, body) =>
        Some((Seq(body), (es: Seq[Expr]) => Forall(args, es.head)))

      /* Binary operators */
      case LetDef(fds, rest) => Some((
        fds.map(_.fullBody) ++ Seq(rest),
        (es: Seq[Expr]) => {
          for((fd, i) <- fds.zipWithIndex) {
            fd.fullBody = es(i)
          }
          LetDef(fds, es(fds.length))
        }
      ))
      case Equals(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => Equals(es(0), es(1)))
      case Implies(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => Implies(es(0), es(1)))
      case Plus(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => Plus(es(0), es(1)))
      case Minus(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => Minus(es(0), es(1)))
      case Times(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => Times(es(0), es(1)))
      case Division(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => Division(es(0), es(1)))
      case Remainder(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => Remainder(es(0), es(1)))
      case Modulo(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => Modulo(es(0), es(1)))
      case LessThan(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => LessThan(es(0), es(1)))
      case GreaterThan(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => GreaterThan(es(0), es(1)))
      case LessEquals(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => LessEquals(es(0), es(1)))
      case GreaterEquals(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => GreaterEquals(es(0), es(1)))
      case BVPlus(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => BVPlus(es(0), es(1)))
      case BVMinus(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => BVMinus(es(0), es(1)))
      case BVTimes(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => BVTimes(es(0), es(1)))
      case BVDivision(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => BVDivision(es(0), es(1)))
      case BVRemainder(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => BVRemainder(es(0), es(1)))
      case BVAnd(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => BVAnd(es(0), es(1)))
      case BVOr(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => BVOr(es(0), es(1)))
      case BVXOr(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => BVXOr(es(0), es(1)))
      case BVShiftLeft(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => BVShiftLeft(es(0), es(1)))
      case BVAShiftRight(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => BVAShiftRight(es(0), es(1)))
      case BVLShiftRight(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => BVLShiftRight(es(0), es(1)))
      case RealPlus(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => RealPlus(es(0), es(1)))
      case RealMinus(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => RealMinus(es(0), es(1)))
      case RealTimes(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => RealTimes(es(0), es(1)))
      case RealDivision(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => RealDivision(es(0), es(1)))
      case StringConcat(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => StringConcat(es(0), es(1)))
      case SetAdd(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => SetAdd(es(0), es(1)))
      case ElementOfSet(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => ElementOfSet(es(0), es(1)))
      case SubsetOf(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => SubsetOf(es(0), es(1)))
      case SetIntersection(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => SetIntersection(es(0), es(1)))
      case SetUnion(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => SetUnion(es(0), es(1)))
      case SetDifference(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => SetDifference(es(0), es(1)))
      case BagAdd(e1, e2) =>
        Some(Seq(e1, e2), (es: Seq[Expr]) => BagAdd(es(0), es(1)))
      case MultiplicityInBag(e1, e2) =>
        Some(Seq(e1, e2), (es: Seq[Expr]) => MultiplicityInBag(es(0), es(1)))
      case BagIntersection(e1, e2) =>
        Some(Seq(e1, e2), (es: Seq[Expr]) => BagIntersection(es(0), es(1)))
      case BagUnion(e1, e2) =>
        Some(Seq(e1, e2), (es: Seq[Expr]) => BagUnion(es(0), es(1)))
      case BagDifference(e1, e2) =>
        Some(Seq(e1, e2), (es: Seq[Expr]) => BagDifference(es(0), es(1)))
      case mg @ MapApply(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => MapApply(es(0), es(1)))
      case MapUnion(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => MapUnion(es(0), es(1)))
      case MapDifference(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => MapDifference(es(0), es(1)))
      case MapIsDefinedAt(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => MapIsDefinedAt(es(0), es(1)))
      case ArraySelect(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => ArraySelect(es(0), es(1)))
      case Let(binder, e, body) =>
        Some(Seq(e, body), (es: Seq[Expr]) => Let(binder, es(0), es(1)))
      case Require(pre, body) =>
        Some(Seq(pre, body), (es: Seq[Expr]) => Require(es(0), es(1)))
      case Ensuring(body, post) =>
        Some(Seq(body, post), (es: Seq[Expr]) => Ensuring(es(0), es(1)))
      case Assert(const, oerr, body) =>
        Some(Seq(const, body), (es: Seq[Expr]) => Assert(es(0), oerr, es(1)))

      /* Other operators */
      case fi @ FunctionInvocation(fd, args) => Some((args, FunctionInvocation(fd, _)))
      case mi @ MethodInvocation(rec, cd, tfd, args) => Some((rec +: args, as => MethodInvocation(as.head, cd, tfd, as.tail)))
      case fa @ Application(caller, args) => Some(caller +: args, as => Application(as.head, as.tail))
      case CaseClass(cd, args) => Some((args, CaseClass(cd, _)))
      case And(args) => Some((args, es => And(es)))
      case Or(args) => Some((args, es => Or(es)))
      case SubString(t1, a, b) => Some((t1::a::b::Nil, es => SubString(es(0), es(1), es(2))))
      case BigSubString(t1, a, b) => Some((t1::a::b::Nil, es => BigSubString(es(0), es(1), es(2))))
      case FiniteSet(els, base) =>
        Some((els.toSeq, els => FiniteSet(els.toSet, base)))
      case FiniteBag(els, base) =>
        val subArgs = els.flatMap { case (k, v) => Seq(k, v) }.toSeq
        val builder = (as: Seq[Expr]) => {
          def rec(kvs: Seq[Expr]): Map[Expr, Expr] = kvs match {
            case Seq(k, v, t @ _*) =>
              Map(k -> v) ++ rec(t)
            case Seq() => Map()
            case _ => sys.error("odd number of key/value expressions")
          }
          FiniteBag(rec(as), base)
        }
        Some((subArgs, builder))
      case FiniteMap(args, f, t) => {
        val subArgs = args.flatMap { case (k, v) => Seq(k, v) }.toSeq
        val builder = (as: Seq[Expr]) => {
          def rec(kvs: Seq[Expr]): Map[Expr, Expr] = kvs match {
            case Seq(k, v, t @ _*) =>
              Map(k -> v) ++ rec(t)
            case Seq() => Map()
            case _ => sys.error("odd number of key/value expressions")
          }
          FiniteMap(rec(as), f, t)
        }
        Some((subArgs, builder))
      }
      case ArrayUpdated(t1, t2, t3) => Some((
        Seq(t1, t2, t3),
        (as: Seq[Expr]) => ArrayUpdated(as(0), as(1), as(2))
      ))
      case NonemptyArray(elems, Some((default, length))) =>
        val elemsSeq: Seq[(Int, Expr)] = elems.toSeq
        val all = elemsSeq.map(_._2) :+ default :+ length
        Some((all, as => {
          val l = as.length
          NonemptyArray(elemsSeq.map(_._1).zip(as.take(l - 2)).toMap, 
                        Some((as(l - 2), as(l - 1))))
        }))
      case na @ NonemptyArray(elems, None) =>
        val ArrayType(tpe) = na.getType
        val (indexes, elsOrdered) = elems.toSeq.unzip

        Some((
          elsOrdered,
          es => NonemptyArray(indexes.zip(es).toMap, None)
        ))
      case Tuple(args) => Some((args, es => Tuple(es)))
      case IfExpr(cond, thenn, elze) => Some((
        Seq(cond, thenn, elze),
        { case Seq(c, t, e) => IfExpr(c, t, e) }
      ))
      case m@MatchExpr(scrut, cases) => Some((
        scrut +: cases.flatMap { _.expressions },
        (es: Seq[Expr]) => {
          var i = 1
          val newcases = for (caze <- cases) yield caze match {
            case SimpleCase(b, _) => i += 1; SimpleCase(b, es(i - 1))
            case GuardedCase(b, _, _) => i += 2; GuardedCase(b, es(i - 2), es(i - 1))
          }

          MatchExpr(es.head, newcases)
        }
      ))
      case Passes(in, out, cases) => Some((
        in +: out +: cases.flatMap { _.expressions },
        {
          case Seq(in, out, es@_*) => {
            var i = 0
            val newcases = for (caze <- cases) yield caze match {
              case SimpleCase(b, _) => i += 1; SimpleCase(b, es(i - 1))
              case GuardedCase(b, _, _) => i += 2; GuardedCase(b, es(i - 2), es(i - 1))
            }

            Passes(in, out, newcases)
          }
        }
      ))

      /* Terminals */
      case t: Terminal => Some(Seq[Expr](), (_:Seq[Expr]) => t)

      /* Expr's not handled here should implement this trait */
      case e: Extractable =>
        e.extract

      case _ =>
        None
    }
  }
  
  // Extractors for types are available at Types.NAryType

  trait Extractable {
    def extract: Option[(Seq[Expr], Seq[Expr] => Expr)]
  }
  
  object TopLevelOrs { // expr1 AND (expr2 AND (expr3 AND ..)) => List(expr1, expr2, expr3)
    def unapply(e: Expr): Option[Seq[Expr]] = e match {
      case Let(i, e, TopLevelOrs(bs)) => Some(bs map (let(i,e,_)))
      case Or(exprs) =>
        Some(exprs.flatMap(unapply).flatten)
      case e =>
        Some(Seq(e))
    }
  }
  object TopLevelAnds { // expr1 AND (expr2 AND (expr3 AND ..)) => List(expr1, expr2, expr3)
    def unapply(e: Expr): Option[Seq[Expr]] = e match {
      case Let(i, e, TopLevelAnds(bs)) => Some(bs map (let(i,e,_)))
      case And(exprs) =>
        Some(exprs.flatMap(unapply).flatten)
      case e =>
        Some(Seq(e))
    }
  }

  object IsTyped {
    def unapply[T <: Typed](e: T): Option[(T, TypeTree)] = Some((e, e.getType))
  }
  
  object WithStringconverter {
    def unapply(t: TypeTree): Option[Expr => Expr] = t match {
      case BooleanType => Some(BooleanToString)
      case Int32Type   => Some(Int32ToString)
      case IntegerType => Some(IntegerToString)
      case CharType    => Some(CharToString)
      case RealType    => Some(RealToString)
      case _           => None
    }
  }

  object FiniteArray {
    def unapply(e: Expr): Option[(Map[Int, Expr], Option[Expr], Expr)] = e match {
      case EmptyArray(_) => 
        Some((Map(), None, IntLiteral(0)))
      case NonemptyArray(els, Some((default, length))) =>
        Some((els, Some(default), length))
      case NonemptyArray(els, None) =>
        Some((els, None, IntLiteral(els.size)))
      case _ => 
        None
    }
  }

  object SimpleCase {
    def apply(p : Pattern, rhs : Expr) = MatchCase(p, None, rhs)
    def unapply(c : MatchCase) = c match {
      case MatchCase(p, None, rhs) => Some((p, rhs))
      case _ => None
    }
  }
  
  object GuardedCase {
    def apply(p : Pattern, g: Expr, rhs : Expr) = MatchCase(p, Some(g), rhs)
    def unapply(c : MatchCase) = c match {
      case MatchCase(p, Some(g), rhs) => Some((p, g, rhs))
      case _ => None
    }
  }
  
  object Pattern {
    def unapply(p : Pattern) : Option[(
      Option[Identifier], 
      Seq[Pattern], 
      (Option[Identifier], Seq[Pattern]) => Pattern
    )] = Option(p) map {
      case InstanceOfPattern(b, ct)       => (b, Seq(), (b, _)  => InstanceOfPattern(b,ct))
      case WildcardPattern(b)             => (b, Seq(), (b, _)  => WildcardPattern(b))
      case CaseClassPattern(b, ct, subs)  => (b, subs,  (b, sp) => CaseClassPattern(b, ct, sp))
      case TuplePattern(b,subs)           => (b, subs,  (b, sp) => TuplePattern(b, sp))
      case LiteralPattern(b, l)           => (b, Seq(), (b, _)  => LiteralPattern(b, l))
      case UnapplyPattern(b, fd, subs)    => (b, subs,  (b, sp) => UnapplyPattern(b, fd, sp))
    }
  }

  def unwrapTuple(e: Expr, isTuple: Boolean): Seq[Expr] = e.getType match {
    case TupleType(subs) if isTuple => 
      for (ind <- 1 to subs.size) yield { tupleSelect(e, ind, isTuple) }      
    case _ if !isTuple => Seq(e)
    case tp => sys.error(s"Calling unwrapTuple on non-tuple $e of type $tp")
  }
  def unwrapTuple(e: Expr, expectedSize: Int): Seq[Expr] = unwrapTuple(e, expectedSize > 1)

  def unwrapTupleType(tp: TypeTree, isTuple: Boolean): Seq[TypeTree] = tp match {
    case TupleType(subs) if isTuple => subs
    case tp if !isTuple => Seq(tp)
    case tp => sys.error(s"Calling unwrapTupleType on $tp")
  }
  def unwrapTupleType(tp: TypeTree, expectedSize: Int): Seq[TypeTree] =
    unwrapTupleType(tp, expectedSize > 1)

  def unwrapTuplePattern(p: Pattern, isTuple: Boolean): Seq[Pattern] = p match {
    case TuplePattern(_, subs) if isTuple => subs
    case tp if !isTuple => Seq(tp)
    case tp => sys.error(s"Calling unwrapTuplePattern on $p")
  }
  def unwrapTuplePattern(p: Pattern, expectedSize: Int): Seq[Pattern] =
    unwrapTuplePattern(p, expectedSize > 1)
  
  object LetPattern {
    def apply(patt : Pattern, value: Expr, body: Expr) : Expr = {
      patt match {
        case WildcardPattern(Some(binder)) => Let(binder, value, body)
        case _ => MatchExpr(value, List(SimpleCase(patt, body)))
      }
    }

    def unapply(me : MatchExpr) : Option[(Pattern, Expr, Expr)] = {
      Option(me) collect {
        case MatchExpr(scrut, List(SimpleCase(pattern, body))) if !aliased(pattern.binders, ExprOps.variablesOf(scrut)) =>
          ( pattern, scrut, body )
      }
    }
  }

  object LetTuple {
    def unapply(me : MatchExpr) : Option[(Seq[Identifier], Expr, Expr)] = {
      Option(me) collect {
        case LetPattern(TuplePattern(None,subPatts), value, body) if
            subPatts forall { case WildcardPattern(Some(_)) => true; case _ => false } => 
          (subPatts map { _.binder.get }, value, body )
      }
    }
  }
}
