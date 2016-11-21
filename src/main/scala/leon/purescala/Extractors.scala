/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import Expressions._
import Common._
import Types._
import Constructors._
import scala.collection.immutable.HashMap

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
    private val table = HashMap[Class[_], Expr => (Seq[Expr], Seq[Expr] => Expr)] (
      classOf[Not] -> { (expr: Expr) =>
        val Not(t) = expr
        (Seq(t), (es: Seq[Expr]) => Not(es.head))
      },
      classOf[Choose] -> { (expr: Expr) =>
        val Choose(ce) = expr
        (Seq(ce), (es: Seq[Expr]) => Choose(es.head))
      },
      classOf[UMinus] -> { (expr: Expr) =>
        val UMinus(t) = expr
        (Seq(t), (es: Seq[Expr]) => UMinus(es.head))
      },
      classOf[BVUMinus] -> { (expr: Expr) =>
        val BVUMinus(t) = expr
        (Seq(t), (es: Seq[Expr]) => BVUMinus(es.head))
      },
      classOf[RealUMinus] -> { (expr: Expr) =>
        val RealUMinus(t) = expr
        (Seq(t), (es: Seq[Expr]) => RealUMinus(es.head))
      },
      classOf[BVNot] -> { (expr: Expr) =>
        val BVNot(t) = expr
        (Seq(t), (es: Seq[Expr]) => BVNot(es.head))
      },
      classOf[StringLength] -> { (expr: Expr) =>
        val StringLength(t) = expr
        (Seq(t), (es: Seq[Expr]) => StringLength(es.head))
      },
      classOf[StringBigLength] -> { (expr: Expr) =>
        val StringBigLength(t) = expr
        (Seq(t), (es: Seq[Expr]) => StringBigLength(es.head))
      },
      classOf[Int32ToString] -> { (expr: Expr) =>
        val Int32ToString(t) = expr
        (Seq(t), (es: Seq[Expr]) => Int32ToString(es.head))
      },
      classOf[BooleanToString] -> { (expr: Expr) =>
        val BooleanToString(t) = expr
        (Seq(t), (es: Seq[Expr]) => BooleanToString(es.head))
      },
      classOf[IntegerToString] -> { (expr: Expr) =>
        val IntegerToString(t) = expr
        (Seq(t), (es: Seq[Expr]) => IntegerToString(es.head))
      },
      classOf[CharToString] -> { (expr: Expr) =>
        val CharToString(t) = expr
        (Seq(t), (es: Seq[Expr]) => CharToString(es.head))
      },
      classOf[RealToString] -> { (expr: Expr) =>
        val RealToString(t) = expr
        (Seq(t), (es: Seq[Expr]) => RealToString(es.head))
      },
      classOf[SetCardinality] -> { (expr: Expr) =>
        val SetCardinality(t) = expr
        (Seq(t), (es: Seq[Expr]) => SetCardinality(es.head))
      },
      classOf[CaseClassSelector] -> { (expr: Expr) =>
        val CaseClassSelector(cd, e, sel) = expr
        (Seq(e), (es: Seq[Expr]) => CaseClassSelector(cd, es.head, sel))
      },
      classOf[IsInstanceOf] -> { (expr: Expr) =>
        val IsInstanceOf(e, ct) = expr
        (Seq(e), (es: Seq[Expr]) => IsInstanceOf(es.head, ct))
      },
      classOf[AsInstanceOf] -> { (expr: Expr) =>
        val AsInstanceOf(e, ct) = expr
        (Seq(e), (es: Seq[Expr]) => AsInstanceOf(es.head, ct))
      },
      classOf[TupleSelect] -> { (expr: Expr) =>
        val TupleSelect(t, i) = expr
        (Seq(t), (es: Seq[Expr]) => TupleSelect(es.head, i))
      },
      classOf[ArrayLength] -> { (expr: Expr) =>
        val ArrayLength(a) = expr
        (Seq(a), (es: Seq[Expr]) => ArrayLength(es.head))
      },
      classOf[Lambda] -> { (expr: Expr) =>
        val Lambda(args, body) = expr
        (Seq(body), (es: Seq[Expr]) => Lambda(args, es.head))
      },
      classOf[FiniteLambda] -> { (expr: Expr) =>
        val FiniteLambda(mapping, dflt, tpe) = expr
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
        (subArgs :+ dflt, builder)
      },
      classOf[Forall] -> { (expr: Expr) =>
        val Forall(args, body) = expr
        (Seq(body), (es: Seq[Expr]) => Forall(args, es.head))

      /* Binary operators */
      },
      classOf[LetDef] -> { (expr: Expr) =>
        val LetDef(fds, rest) = expr
        (
          fds.map(_.fullBody) ++ Seq(rest),
          (es: Seq[Expr]) => {
            for ((fd, i) <- fds.zipWithIndex) {
              fd.fullBody = es(i)
            }
            LetDef(fds, es(fds.length))
          }
          )
      },
      classOf[Equals] -> { (expr: Expr) =>
        val Equals(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => Equals(es(0), es(1)))
      },
      classOf[Implies] -> { (expr: Expr) =>
        val Implies(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => Implies(es(0), es(1)))
      },
      classOf[Plus] -> { (expr: Expr) =>
        val Plus(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => Plus(es(0), es(1)))
      },
      classOf[Minus] -> { (expr: Expr) =>
        val Minus(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => Minus(es(0), es(1)))
      },
      classOf[Times] -> { (expr: Expr) =>
        val Times(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => Times(es(0), es(1)))
      },
      classOf[Division] -> { (expr: Expr) =>
        val Division(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => Division(es(0), es(1)))
      },
      classOf[Remainder] -> { (expr: Expr) =>
        val Remainder(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => Remainder(es(0), es(1)))
      },
      classOf[Modulo] -> { (expr: Expr) =>
        val Modulo(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => Modulo(es(0), es(1)))
      },
      classOf[LessThan] -> { (expr: Expr) =>
        val LessThan(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => LessThan(es(0), es(1)))
      },
      classOf[GreaterThan] -> { (expr: Expr) =>
        val GreaterThan(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => GreaterThan(es(0), es(1)))
      },
      classOf[LessEquals] -> { (expr: Expr) =>
        val LessEquals(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => LessEquals(es(0), es(1)))
      },
      classOf[GreaterEquals] -> { (expr: Expr) =>
        val GreaterEquals(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => GreaterEquals(es(0), es(1)))
      },
      classOf[BVPlus] -> { (expr: Expr) =>
        val BVPlus(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => BVPlus(es(0), es(1)))
      },
      classOf[BVMinus] -> { (expr: Expr) =>
        val BVMinus(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => BVMinus(es(0), es(1)))
      },
      classOf[BVTimes] -> { (expr: Expr) =>
        val BVTimes(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => BVTimes(es(0), es(1)))
      },
      classOf[BVDivision] -> { (expr: Expr) =>
        val BVDivision(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => BVDivision(es(0), es(1)))
      },
      classOf[BVRemainder] -> { (expr: Expr) =>
        val BVRemainder(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => BVRemainder(es(0), es(1)))
      },
      classOf[BVAnd] -> { (expr: Expr) =>
        val BVAnd(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => BVAnd(es(0), es(1)))
      },
      classOf[BVOr] -> { (expr: Expr) =>
        val BVOr(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => BVOr(es(0), es(1)))
      },
      classOf[BVXOr] -> { (expr: Expr) =>
        val BVXOr(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => BVXOr(es(0), es(1)))
      },
      classOf[BVShiftLeft] -> { (expr: Expr) =>
        val BVShiftLeft(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => BVShiftLeft(es(0), es(1)))
      },
      classOf[BVAShiftRight] -> { (expr: Expr) =>
        val BVAShiftRight(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => BVAShiftRight(es(0), es(1)))
      },
      classOf[BVLShiftRight] -> { (expr: Expr) =>
        val BVLShiftRight(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => BVLShiftRight(es(0), es(1)))
      },
      classOf[RealPlus] -> { (expr: Expr) =>
        val RealPlus(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => RealPlus(es(0), es(1)))
      },
      classOf[RealMinus] -> { (expr: Expr) =>
        val RealMinus(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => RealMinus(es(0), es(1)))
      },
      classOf[RealTimes] -> { (expr: Expr) =>
        val RealTimes(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => RealTimes(es(0), es(1)))
      },
      classOf[RealDivision] -> { (expr: Expr) =>
        val RealDivision(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => RealDivision(es(0), es(1)))
      },
      classOf[StringConcat] -> { (expr: Expr) =>
        val StringConcat(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => StringConcat(es(0), es(1)))
      },
      classOf[SetAdd] -> { (expr: Expr) =>
        val SetAdd(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => SetAdd(es(0), es(1)))
      },
      classOf[ElementOfSet] -> { (expr: Expr) =>
        val ElementOfSet(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => ElementOfSet(es(0), es(1)))
      },
      classOf[SubsetOf] -> { (expr: Expr) =>
        val SubsetOf(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => SubsetOf(es(0), es(1)))
      },
      classOf[SetIntersection] -> { (expr: Expr) =>
        val SetIntersection(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => SetIntersection(es(0), es(1)))
      },
      classOf[SetUnion] -> { (expr: Expr) =>
        val SetUnion(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => SetUnion(es(0), es(1)))
      },
      classOf[SetDifference] -> { (expr: Expr) =>
        val SetDifference(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => SetDifference(es(0), es(1)))
      },
      classOf[BagAdd] -> { (expr: Expr) =>
        val BagAdd(e1, e2) = expr
        (Seq(e1, e2), (es: Seq[Expr]) => BagAdd(es(0), es(1)))
      },
      classOf[MultiplicityInBag] -> { (expr: Expr) =>
        val MultiplicityInBag(e1, e2) = expr
        (Seq(e1, e2), (es: Seq[Expr]) => MultiplicityInBag(es(0), es(1)))
      },
      classOf[BagIntersection] -> { (expr: Expr) =>
        val BagIntersection(e1, e2) = expr
        (Seq(e1, e2), (es: Seq[Expr]) => BagIntersection(es(0), es(1)))
      },
      classOf[BagUnion] -> { (expr: Expr) =>
        val BagUnion(e1, e2) = expr
        (Seq(e1, e2), (es: Seq[Expr]) => BagUnion(es(0), es(1)))
      },
      classOf[BagDifference] -> { (expr: Expr) =>
        val BagDifference(e1, e2) = expr
        (Seq(e1, e2), (es: Seq[Expr]) => BagDifference(es(0), es(1)))
      },
      classOf[MapApply] -> { (expr: Expr) =>
        val MapApply(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => MapApply(es(0), es(1)))
      },
      classOf[MapUnion] -> { (expr: Expr) =>
        val MapUnion(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => MapUnion(es(0), es(1)))
      },
      classOf[MapDifference] -> { (expr: Expr) =>
        val MapDifference(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => MapDifference(es(0), es(1)))
      },
      classOf[MapIsDefinedAt] -> { (expr: Expr) =>
        val MapIsDefinedAt(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => MapIsDefinedAt(es(0), es(1)))
      },
      classOf[ArraySelect] -> { (expr: Expr) =>
        val ArraySelect(t1, t2) = expr
        (Seq(t1, t2), (es: Seq[Expr]) => ArraySelect(es(0), es(1)))
      },
      classOf[Let] -> { (expr: Expr) =>
        val Let(binder, e, body) = expr
        (Seq(e, body), (es: Seq[Expr]) => Let(binder, es(0), es(1)))
      },
      classOf[Require] -> { (expr: Expr) =>
        val Require(pre, body) = expr
        (Seq(pre, body), (es: Seq[Expr]) => Require(es(0), es(1)))
      },
      classOf[Ensuring] -> { (expr: Expr) =>
        val Ensuring(body, post) = expr
        (Seq(body, post), (es: Seq[Expr]) => Ensuring(es(0), es(1)))
      },
      classOf[Assert] -> { (expr: Expr) =>
        val Assert(const, oerr, body) = expr
        (Seq(const, body), (es: Seq[Expr]) => Assert(es(0), oerr, es(1)))
      },
      classOf[FunctionInvocation] -> { (expr: Expr) =>
        val FunctionInvocation(fd, args) = expr
        (args, FunctionInvocation(fd, _))
      },
      classOf[MethodInvocation] -> { (expr: Expr) =>
        val MethodInvocation(rec, cd, tfd, args) = expr
        (rec +: args, as => MethodInvocation(as.head, cd, tfd, as.tail))
      },
      classOf[Application] -> { (expr: Expr) =>
        val Application(caller, args) = expr
        (caller +: args, as => Application(as.head, as.tail))
      },
      classOf[CaseClass] -> { (expr: Expr) =>
        val CaseClass(cd, args) = expr
        (args, CaseClass(cd, _))
      },
      classOf[And] -> { (expr: Expr) =>
        val And(args) = expr
        (args, es => And(es))
      },
      classOf[Or] -> { (expr: Expr) =>
        val Or(args) = expr
        (args, es => Or(es))
      },
      classOf[SubString] -> { (expr: Expr) =>
        val SubString(t1, a, b) = expr
        (t1 :: a :: b :: Nil, es => SubString(es(0), es(1), es(2)))
      },
      classOf[BigSubString] -> { (expr: Expr) =>
        val BigSubString(t1, a, b) = expr
        (t1 :: a :: b :: Nil, es => BigSubString(es(0), es(1), es(2)))
      },
      classOf[FiniteSet] -> { (expr: Expr) =>
        val FiniteSet(els, base) = expr
        (els.toSeq, els => FiniteSet(els.toSet, base))
      },
      classOf[FiniteBag] -> { (expr: Expr) =>
        val FiniteBag(els, base) = expr
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
        (subArgs, builder)
      },
      classOf[FiniteMap] -> { (expr: Expr) =>
        val FiniteMap(args, f, t) = expr
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
        (subArgs, builder)
      
      },
      classOf[ArrayUpdated] -> { (expr: Expr) =>
        val ArrayUpdated(t1, t2, t3) = expr
        (Seq(t1, t2, t3), (as: Seq[Expr]) => ArrayUpdated(as(0), as(1), as(2)))
      },
      classOf[NonemptyArray] -> { (expr: Expr) =>
        expr match {
          case NonemptyArray(elems, None) =>
            val ArrayType(tpe) = expr.getType
            val (indexes, elsOrdered) = elems.toSeq.unzip
            (elsOrdered, es => NonemptyArray(indexes.zip(es).toMap, None))
          case NonemptyArray(elems, Some((default, length))) =>
            val elemsSeq: Seq[(Int, Expr)] = elems.toSeq
            val all = elemsSeq.map(_._2) :+ default :+ length
            (all, as => {
              val l = as.length
              NonemptyArray(elemsSeq.map(_._1).zip(as.take(l - 2)).toMap,
                Some((as(l - 2), as(l - 1))))
            })
        }
      },
      classOf[Tuple] -> { (expr: Expr) =>
        val Tuple(args) = expr
        (args, es => Tuple(es))

      },
      classOf[ArrayForall] -> { (expr: Expr) =>
        val ArrayForall(array, from, to, pred) = expr
        (
          Seq(array, from, to, pred),
          (as: Seq[Expr]) => ArrayForall(as(0), as(1), as(2), as(3))
          )
      },
      classOf[ArrayExists] -> { (expr: Expr) =>
        val ArrayExists(array, from, to, pred) = expr
        (
          Seq(array, from, to, pred),
          (as: Seq[Expr]) => ArrayExists(as(0), as(1), as(2), as(3))
          )

      },
      classOf[BoundedForall] -> { (expr: Expr) =>
        val BoundedForall(from, to, pred) = expr
        (
          Seq(from, to, pred),
          (as: Seq[Expr]) => BoundedForall(as(0), as(1), as(2))
          )
      },
      classOf[BoundedExists] -> { (expr: Expr) =>
        val BoundedExists(from, to, pred) = expr
        (
          Seq(from, to, pred),
          (as: Seq[Expr]) => BoundedExists(as(0), as(1), as(2))
        )

      },
      classOf[IfExpr] -> { (expr: Expr) =>
        val IfExpr(cond, thenn, elze) = expr
        (
          Seq(cond, thenn, elze),
          { case Seq(c, t, e) => IfExpr(c, t, e) }
        )
      },
      classOf[MatchExpr] -> { (expr: Expr) =>
        val MatchExpr(scrut, cases) = expr
        (
          scrut +: cases.flatMap { _.expressions },
          (es: Seq[Expr]) => {
            var i = 1
            val newcases = for (caze <- cases) yield caze match {
              case SimpleCase(b, _) => i += 1; SimpleCase(b, es(i - 1))
              case GuardedCase(b, _, _) => i += 2; GuardedCase(b, es(i - 2), es(i - 1))
            }

            MatchExpr(es.head, newcases)
          }
        )
      },
      classOf[Passes] -> { (expr: Expr) =>
        val Passes(in, out, cases) = expr
        (
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
        )
      }

    )

    def unapply(expr: Expr): Option[(Seq[Expr], (Seq[Expr]) => Expr)] = expr match {

      /* Terminals */
      case t: Terminal =>
        Some(Seq[Expr](), (_:Seq[Expr]) => t)
      
      case e: Extractable =>
        e.extract

      case other =>
        table.get(expr.getClass).map(_(expr))
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
