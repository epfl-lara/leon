/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package smtlib

import purescala.Common._
import purescala.Expressions._
import purescala.Constructors._
import purescala.Types._
import purescala.Definitions._

import _root_.smtlib.parser.Terms.{Identifier => SMTIdentifier, _}
import _root_.smtlib.parser.Commands.{FunDef => SMTFunDef, _}
import _root_.smtlib.interpreters.Z3Interpreter
import _root_.smtlib.theories.Core.{Equals => SMTEquals, _}
import _root_.smtlib.theories.ArraysEx

import utils.Bijection

trait SMTLIBZ3Target extends SMTLIBTarget {

  def targetName = "z3"

  def interpreterOps(ctx: LeonContext) = {
    Seq(
      "-in",
      "-smt2"
    )
  }

  def getNewInterpreter(ctx: LeonContext) = {
    val opts = interpreterOps(ctx)
    reporter.debug("Invoking solver "+targetName+" with "+opts.mkString(" "))

    new Z3Interpreter("z3", opts.toArray)
  }

  protected val extSym = SSymbol("_")

  protected var setSort: Option[SSymbol] = None

  override protected def declareSort(t: TypeTree): Sort = {
    val tpe = normalizeType(t)
    sorts.cachedB(tpe) {
      tpe match {
        case SetType(base) =>
          super.declareSort(BooleanType)
          declareSetSort(base)
        case _ =>
          super.declareSort(t)
      }
    }
  }

  protected def declareSetSort(of: TypeTree): Sort = {
    setSort match {
      case None =>
        val s = SSymbol("Set")
        val t = SSymbol("T")
        setSort = Some(s)

        val arraySort = Sort(SMTIdentifier(SSymbol("Array")), 
                             Seq(Sort(SMTIdentifier(t)), BoolSort()))

        val cmd = DefineSort(s, Seq(t), arraySort)
        emit(cmd)

      case _ =>
    }

    Sort(SMTIdentifier(setSort.get), Seq(declareSort(of)))
  }

  val stringBijection = new Bijection[String, CaseClass]()
  
  lazy val cons = program.lookup("leon.collection.Cons") match {
    case Some(cc@CaseClassDef(id, tparams, parent, _)) => cc.typed
    case _ => throw new Exception("Could not find Cons in Z3 solver")
  }
  lazy val nil = program.lookup("leon.collection.Nil") match {
    case Some(cc@CaseClassDef(id, tparams, parent, _)) => cc.typed
    case _ => throw new Exception("Could not find Nil in Z3 solver")
  }
  lazy val list = program.lookup("leon.collection.List") match {
    case Some(cc@AbstractClassDef(id, tparams, parent)) => cc.typed
    case _ => throw new Exception("Could not find List in Z3 solver")
  }
  def extractFunDef(s: String): FunDef = program.lookup(s) match {
    case Some(fd: FunDef) => fd
    case _ => throw new Exception("Could not find "+s+" in Z3 solver")
  }
  lazy val list_size = extractFunDef("leon.collection.List.size")
  lazy val list_++ = extractFunDef("leon.collection.List.++")
  lazy val list_take = extractFunDef("leon.collection.List.take")
  lazy val list_drop = extractFunDef("leon.collection.List.drop")
  lazy val list_slice = extractFunDef("leon.collection.List.slice")
  
  
  override protected def fromSMT(t: Term, otpe: Option[TypeTree] = None)
                                (implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): Expr = {
    (t, otpe) match {
      case (SimpleSymbol(s), Some(tp: TypeParameter)) =>
        val n = s.name.split("!").toList.last
        GenericValue(tp, n.toInt)

      case (QualifiedIdentifier(ExtendedIdentifier(SSymbol("as-array"), k: SSymbol), _), Some(tpe)) =>
        if (letDefs contains k) {
          // Need to recover value form function model
          fromRawArray(extractRawArray(letDefs(k), tpe), tpe)
        } else {
          throw LeonFatalError("Array on non-function or unknown symbol "+k)
        }

      case (FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("const"), _), Some(ArraysEx.ArraySort(k, v))),
        Seq(defV)
      ), Some(tpe)) =>
        val ktpe = sorts.fromB(k)
        val vtpe = sorts.fromB(v)

        fromRawArray(RawArrayValue(ktpe, Map(), fromSMT(defV, vtpe)), tpe)

      case (SimpleSymbol(s), Some(StringType)) if constructors.containsB(s) =>
        constructors.toA(s) match {
          case cct: CaseClassType if cct == nil =>
            StringLiteral("")
          case t =>
            unsupported(t, "woot? for a single constructor for non-case-object")
        }
      case (FunctionApplication(SimpleSymbol(s), args), Some(StringType)) if constructors.containsB(s) =>
        constructors.toA(s) match {
          case cct: CaseClassType if cct == cons =>
            val rargs = args.zip(cct.fields.map(_.getType)).map(fromSMT)
            val s = ("" /: rargs)  {
              case (acc, c@CharLiteral(s)) => acc + s
              case _ => unsupported(cct, "Cannot extract string out of list of any")
            }
            StringLiteral(s)
          case t => unsupported(t, "Cannot extract string")
        }

      /*case (Strings.Length(a), _) =>
        val aa = fromSMT(a)
        StringLength(aa)

      case (Strings.Concat(a, b, c @ _*), _) =>
        val aa = fromSMT(a)
        val bb = fromSMT(b)
        (StringConcat(aa, bb) /: c.map(fromSMT(_))) {
          case (s, cc) => StringConcat(s, cc)
        }
      
      case (Strings.Substring(s, start, offset), _) =>
        val ss = fromSMT(s)
        val tt = fromSMT(start)
        val oo = fromSMT(offset)
        oo match {
          case Minus(otherEnd, `tt`) => SubString(ss, tt, otherEnd)
          case _ => SubString(ss, tt, Plus(tt, oo))
        }
        
      case (Strings.At(a, b), _) => fromSMT(Strings.Substring(a, b, SNumeral(1)))
*/

      case _ =>
        super.fromSMT(t, otpe)
    }
  }

  override protected def toSMT(e: Expr)(implicit bindings: Map[Identifier, Term]): Term = e match {

    /**
     * ===== Set operations =====
     */
    case fs @ FiniteSet(elems, base) =>
      declareSort(fs.getType)

      toSMT(RawArrayValue(base, elems.map {
        case k => k -> BooleanLiteral(true)
      }.toMap, BooleanLiteral(false)))

    case SubsetOf(ss, s) =>
      // a isSubset b   ==>   (a zip b).map(implies) == (* => true)
      val allTrue = ArrayConst(declareSort(s.getType), True())

      SMTEquals(ArrayMap(SSymbol("implies"), toSMT(ss), toSMT(s)), allTrue)

    case ElementOfSet(e, s) =>
      ArraysEx.Select(toSMT(s), toSMT(e))

    case SetDifference(a, b) =>
      // a -- b
      // becomes:
      // a && not(b)

      ArrayMap(SSymbol("and"), toSMT(a), ArrayMap(SSymbol("not"), toSMT(b)))

    case SetUnion(l, r) =>
      ArrayMap(SSymbol("or"), toSMT(l), toSMT(r))

    case SetIntersection(l, r) =>
      ArrayMap(SSymbol("and"), toSMT(l), toSMT(r))

    case StringLiteral(v)          =>
      // No string support for z3 at this moment.
      val stringEncoding = stringBijection.cachedB(v) {
        v.toList.foldRight(CaseClass(nil, Seq())){
          case (char, l) => CaseClass(cons, Seq(CharLiteral(char), l))
        }
      }
      toSMT(stringEncoding)
    case StringLength(a)           =>
      toSMT(functionInvocation(list_size, Seq(a)))
    case StringConcat(a, b)        =>
      toSMT(functionInvocation(list_++, Seq(a, b)))
    case SubString(a, start, Plus(start2, length)) if start == start2  =>
      toSMT(functionInvocation(list_take, Seq(functionInvocation(list_drop, Seq(a, start)), length)))
    case SubString(a, start, end)  => 
      toSMT(functionInvocation(list_slice, Seq(a, start, end)))
    case _ =>
      super.toSMT(e)
  }

  protected def extractRawArray(s: DefineFun, tpe: TypeTree)(implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): RawArrayValue = s match {
    case DefineFun(SMTFunDef(a, Seq(SortedVar(arg, akind)), rkind, body)) =>
      val (argTpe, retTpe) = tpe match {
        case SetType(base) => (base, BooleanType)
        case MapType(from, to) => (from, library.optionType(to))
        case ArrayType(base) => (Int32Type, base)
        case FunctionType(args, ret) => (tupleTypeWrap(args), ret)
        case RawArrayType(from, to) => (from, to)
        case _ => unsupported(tpe, "Unsupported type for (un)packing into raw arrays (got kinds "+akind+" -> "+rkind+")")
      }

      def extractCases(e: Term): (Map[Expr, Expr], Expr) = e match {
        case ITE(SMTEquals(SimpleSymbol(`arg`), k), v, e) =>
          val (cs, d) = extractCases(e)
          (Map(fromSMT(k, argTpe) -> fromSMT(v, retTpe)) ++ cs, d)
        case e =>
          (Map(),fromSMT(e, retTpe))
      }

      val (cases, default) = extractCases(body)

      RawArrayValue(argTpe, cases, default)

    case _ =>
      throw LeonFatalError("Unable to extract "+s)
  }

  protected object ArrayMap {
    def apply(op: SSymbol, arrs: Term*) = {
      FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("map"), List(op))),
        arrs
      )
    }
  }

  protected object ArrayConst {
    def apply(sort: Sort, default: Term) = {
      FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("const")), Some(sort)),
        List(default))
    }
  }
}
