/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package smtlib

import utils._
import purescala._
import Common._
import Expressions._
import Extractors._
import ExprOps._
import Types._
import Constructors._
import Definitions._

import _root_.smtlib.common._
import _root_.smtlib.printer.{RecursivePrinter => SMTPrinter}
import _root_.smtlib.parser.Commands.{Constructor => SMTConstructor, FunDef => _, Assert => SMTAssert, _}
import _root_.smtlib.parser.Terms.{
  Forall => SMTForall,
  Exists => SMTExists,
  Identifier => SMTIdentifier,
  Let => SMTLet,
  _
}
import _root_.smtlib.parser.CommandsResponses.{Error => ErrorResponse, _}
import _root_.smtlib.theories._
import _root_.smtlib.{Interpreter => SMTInterpreter}


abstract class SMTLIBSolver(val context: LeonContext,
                            val program: Program) extends Solver with NaiveAssumptionSolver {

  /* Solver name */
  def targetName: String
  override def name: String = "smt-"+targetName

  /* Reporter */
  protected val reporter = context.reporter

  /* Interface with Interpreter */

  protected def interpreterOps(ctx: LeonContext): Seq[String]

  protected def getNewInterpreter(ctx: LeonContext): SMTInterpreter

  protected val interpreter = getNewInterpreter(context)


  /* Printing VCs */
  protected lazy val out: Option[java.io.FileWriter] = if (reporter.isDebugEnabled) Some {
    val file = context.files.headOption.map(_.getName).getOrElse("NA")
    val n    = VCNumbers.getNext(targetName+file)

    val dir = new java.io.File("vcs")

    if (!dir.isDirectory) {
      dir.mkdir
    }

    val fileName = s"smt-sessions/$targetName-$file-$n.smt2"

    reporter.debug(s"Outputting smt session into $fileName" )

    val fw = new java.io.FileWriter(fileName, false)

    fw.write("; Solver : "+name+"\n")
    fw.write("; Options: "+interpreterOps(context).mkString(" ")+"\n")

    fw
  } else None


  /* Interruptible interface */

  private var interrupted = false

  context.interruptManager.registerForInterrupts(this)

  override def interrupt(): Unit = {
    interrupted = true
    interpreter.interrupt()
  }
  override def recoverInterrupt(): Unit = {
    interrupted = false
  }



  /*
   * Translation from Leon Expressions to SMTLIB terms and reverse
   */

  /* Symbol handling */
  protected object SimpleSymbol {
    def unapply(term: Term): Option[SSymbol] = term match {
      case QualifiedIdentifier(SMTIdentifier(sym, Seq()), None) => Some(sym)
      case _ => None
    }
  }

  import scala.language.implicitConversions
  protected implicit def symbolToQualifiedId(s: SSymbol): QualifiedIdentifier = {
    QualifiedIdentifier(SMTIdentifier(s))
  }

  protected val adtManager = new ADTManager(context)

  protected val library = program.library

  protected def id2sym(id: Identifier): SSymbol = SSymbol(id.name+"!"+id.id)

  protected def freshSym(id: Identifier): SSymbol = freshSym(id.name)
  protected def freshSym(name: String): SSymbol = id2sym(FreshIdentifier(name))


  /* Metadata for CC, and variables */
  protected val constructors  = new IncrementalBijection[TypeTree, SSymbol]()
  protected val selectors     = new IncrementalBijection[(TypeTree, Int), SSymbol]()
  protected val testers       = new IncrementalBijection[TypeTree, SSymbol]()
  protected val variables     = new IncrementalBijection[Identifier, SSymbol]()
  protected val genericValues = new IncrementalBijection[GenericValue, SSymbol]()
  protected val sorts         = new IncrementalBijection[TypeTree, Sort]()
  protected val functions     = new IncrementalBijection[TypedFunDef, SSymbol]()
  protected val errors        = new IncrementalBijection[Unit, Boolean]()
  protected def hasError = errors.getB(()) contains true
  protected def addError() = errors += () -> true

  /* Helper functions */

  protected def normalizeType(t: TypeTree): TypeTree = t match {
    case ct: ClassType => ct.root
    case tt: TupleType => tupleTypeWrap(tt.bases.map(normalizeType))
    case _ => t
  }

  protected def quantifiedTerm(
    quantifier: (SortedVar, Seq[SortedVar], Term) => Term,
    vars: Seq[Identifier],
    body: Expr
  ) : Term = {
    if (vars.isEmpty) toSMT(body)(Map())
    else {
      val sortedVars = vars map { id =>
        SortedVar(id2sym(id), declareSort(id.getType))
      }
      quantifier(
        sortedVars.head,
        sortedVars.tail,
        toSMT(body)(vars.map{ id => id -> (id2sym(id): Term)}.toMap)
      )
    }
  }

  // Returns a quantified term where all free variables in the body have been quantified
  protected def quantifiedTerm(quantifier: (SortedVar, Seq[SortedVar], Term) => Term, body: Expr): Term =
    quantifiedTerm(quantifier, variablesOf(body).toSeq, body)

  protected def fromRawArray(r: RawArrayValue, tpe: TypeTree): Expr = tpe match {
    case SetType(base) =>
      if (r.default != BooleanLiteral(false)) {
        unsupported("Co-finite sets are not supported.")
      }
      require(r.keyTpe == base, s"Type error in solver model, expected $base, found ${r.keyTpe}")

      FiniteSet(r.elems.keySet, base)

    case RawArrayType(from, to) =>
      r

    case ft @ FunctionType(from, to) =>
      finiteLambda(r.default, r.elems.toSeq, from)

    case MapType(from, to) =>
      // We expect a RawArrayValue with keys in from and values in Option[to],
      // with default value == None
      if (r.default.getType != library.noneType(to)) {
        unsupported("Co-finite maps are not supported.")
      }
      require(r.keyTpe == from, s"Type error in solver model, expected $from, found ${r.keyTpe}")

      val elems = r.elems.flatMap {
        case (k, CaseClass(leonSome, Seq(x))) => Some(k -> x)
        case (k, _) => None
      }.toSeq
      FiniteMap(elems, from, to)

    case _ =>
      unsupported("Unable to extract from raw array for "+tpe)
  }

  protected def unsupported(str: String) = {
    reporter.warning(s"Unsupported in smt-$targetName: $str")
    throw new IllegalArgumentException(str)
  }

  protected def declareSort(t: TypeTree): Sort = {
    val tpe = normalizeType(t)
    sorts.cachedB(tpe) {
      tpe match {
        case BooleanType => Core.BoolSort()
        case IntegerType => Ints.IntSort()
        case RealType => Reals.RealSort()
        case Int32Type => FixedSizeBitVectors.BitVectorSort(32)
        case CharType => FixedSizeBitVectors.BitVectorSort(32)

        case RawArrayType(from, to) =>
          Sort(SMTIdentifier(SSymbol("Array")), Seq(declareSort(from), declareSort(to)))

        case MapType(from, to) =>
          declareSort(RawArrayType(from, library.optionType(to)))

        case FunctionType(from, to) =>
          Sort(SMTIdentifier(SSymbol("Array")), Seq(declareSort(tupleTypeWrap(from)), declareSort(to)))

        case TypeParameter(id) =>
          val s = id2sym(id)
          val cmd = DeclareSort(s, 0)
          sendCommand(cmd)
          Sort(SMTIdentifier(s))

        case _: ClassType | _: TupleType | _: ArrayType | UnitType =>
          declareStructuralSort(tpe)

        case _ =>
          unsupported("Sort "+t)
      }
    }
  }

  protected def declareDatatypes(datatypes: Map[TypeTree, DataType]): Unit = {
    // We pre-declare ADTs
    for ((tpe, DataType(sym, _)) <- datatypes) {
      sorts += tpe -> Sort(SMTIdentifier(id2sym(sym)))
    }

    def toDecl(c: Constructor): SMTConstructor = {
      val s = id2sym(c.sym)

      testers += c.tpe -> SSymbol("is-"+s.name)
      constructors += c.tpe -> s

      SMTConstructor(s, c.fields.zipWithIndex.map {
        case ((cs, t), i) =>
          selectors += (c.tpe, i) -> id2sym(cs)
          (id2sym(cs), declareSort(t))
      })
    }

    val adts = for ((tpe, DataType(sym, cases)) <- datatypes.toList) yield {
      (id2sym(sym), cases.map(toDecl))
    }

    if (adts.nonEmpty) {
      val cmd = DeclareDatatypes(adts)
      sendCommand(cmd)
    }

  }

  protected def declareStructuralSort(t: TypeTree): Sort = {
    // Populates the dependencies of the structural type to define.
    adtManager.defineADT(t) match {
      case Left(adts) =>
        declareDatatypes(adts)
        sorts.toB(normalizeType(t))

      case Right(conflicts) =>
        conflicts.foreach { declareStructuralSort }
        declareStructuralSort(t)
    }

  }

  protected def declareVariable(id: Identifier): SSymbol = {
    variables.cachedB(id) {
      val s = id2sym(id)
      val cmd = DeclareFun(s, List(), declareSort(id.getType))
      sendCommand(cmd)
      s
    }
  }

  protected def declareFunction(tfd: TypedFunDef): SSymbol = {
    functions.cachedB(tfd) {
      val id = if (tfd.tps.isEmpty) {
        tfd.id
      } else {
        FreshIdentifier(tfd.id.name)
      }
      val s = id2sym(id)
      sendCommand(DeclareFun(
        s,
        tfd.params.map( (p: ValDef) => declareSort(p.getType)),
        declareSort(tfd.returnType)
      ))
      s
    }
  }

  /* Translate a Leon Expr to an SMTLIB term */

  protected def toSMT(e: Expr)(implicit bindings: Map[Identifier, Term]): Term = {
    e match {
      case Variable(id) =>
        declareSort(e.getType)
        bindings.getOrElse(id, variables.toB(id))

      case UnitLiteral() =>
        declareSort(UnitType)

        declareVariable(FreshIdentifier("Unit", UnitType))

      case InfiniteIntegerLiteral(i) => if (i >= 0) Ints.NumeralLit(i) else Ints.Neg(Ints.NumeralLit(-i))
      case IntLiteral(i) => FixedSizeBitVectors.BitVectorLit(Hexadecimal.fromInt(i))
      case RealLiteral(d) => if (d >= 0) Reals.DecimalLit(d) else Reals.Neg(Reals.DecimalLit(-d))
      case CharLiteral(c) => FixedSizeBitVectors.BitVectorLit(Hexadecimal.fromInt(c.toInt))
      case BooleanLiteral(v) => Core.BoolConst(v)
      case Let(b,d,e) =>
        val id      = id2sym(b)
        val value   = toSMT(d)
        val newBody = toSMT(e)(bindings + (b -> id))

        SMTLet(
          VarBinding(id, value),
          Seq(),
          newBody
        )

      case er @ Error(tpe, _) =>
        declareVariable(FreshIdentifier("error_value", tpe))

      case s @ CaseClassSelector(cct, e, id) =>
        declareSort(cct)
        val selector = selectors.toB((cct, s.selectorIndex))
        FunctionApplication(selector, Seq(toSMT(e)))

      case AsInstanceOf(expr, cct) =>
        toSMT(expr)

      case IsInstanceOf(cct, e) =>
        declareSort(cct)
        val cases = cct match {
          case act: AbstractClassType =>
            act.knownCCDescendants
          case cct: CaseClassType =>
            Seq(cct)
        }
        val oneOf = cases map testers.toB
        oneOf match {
          case Seq(tester) =>
            FunctionApplication(tester, Seq(toSMT(e)))
          case more =>
            val es = freshSym("e")
            SMTLet(VarBinding(es, toSMT(e)), Seq(),
              Core.Or(oneOf.map(FunctionApplication(_, Seq(es:Term))): _*)
            )
        }

      case CaseClass(cct, es) =>
        declareSort(cct)
        val constructor = constructors.toB(cct)
        if (es.isEmpty) {
          constructor
        } else {
          FunctionApplication(constructor, es.map(toSMT))
        }

      case t @ Tuple(es) =>
        val tpe = normalizeType(t.getType)
        declareSort(tpe)
        val constructor = constructors.toB(tpe)
        FunctionApplication(constructor, es.map(toSMT))

      case ts @ TupleSelect(t, i) =>
        val tpe = normalizeType(t.getType)
        declareSort(tpe)
        val selector = selectors.toB((tpe, i-1))
        FunctionApplication(selector, Seq(toSMT(t)))

      case al @ ArrayLength(a) =>
        val tpe = normalizeType(a.getType)
        val selector = selectors.toB((tpe, 0))

        FunctionApplication(selector, Seq(toSMT(a)))

      case al @ ArraySelect(a, i) =>
        val tpe = normalizeType(a.getType)

        val scontent = FunctionApplication(selectors.toB((tpe, 1)), Seq(toSMT(a)))

        ArraysEx.Select(scontent, toSMT(i))

      case al @ ArrayUpdated(a, i, e) =>
        val tpe = normalizeType(a.getType)

        val sa = toSMT(a)
        val ssize    = FunctionApplication(selectors.toB((tpe, 0)), Seq(sa))
        val scontent = FunctionApplication(selectors.toB((tpe, 1)), Seq(sa))

        val newcontent = ArraysEx.Store(scontent, toSMT(i), toSMT(e))

        val constructor = constructors.toB(tpe)
        FunctionApplication(constructor, Seq(ssize, newcontent))

      case ra @ RawArrayValue(keyTpe, elems, default) =>
        val s = declareSort(ra.getType)

        var res: Term = FunctionApplication(
          QualifiedIdentifier(SMTIdentifier(SSymbol("const")), Some(s)),
          List(toSMT(default))
        )
        for ((k, v) <- elems) {
          res = ArraysEx.Store(res, toSMT(k), toSMT(v))
        }

        res

      case a @ FiniteArray(elems, oDef, size) =>
        val tpe @ ArrayType(to) = normalizeType(a.getType)
        declareSort(tpe)

        val default: Expr = oDef.getOrElse(simplestValue(to))

        val arr = toSMT(RawArrayValue(Int32Type, elems.map {
          case (k, v) => IntLiteral(k) -> v
        }, default))

        FunctionApplication(constructors.toB(tpe), List(toSMT(size), arr))

      /**
       * ===== Map operations =====
       */
      case m @ FiniteMap(elems, _, _) =>
        val mt @ MapType(from, to) = m.getType
        declareSort(mt)

        toSMT(RawArrayValue(from, elems.map {
          case (k, v) => k -> CaseClass(library.someType(to), Seq(v))
        }.toMap, CaseClass(library.noneType(to), Seq())))


      case MapGet(m, k) =>
        val mt @ MapType(_, to) = m.getType
        declareSort(mt)
        // m(k) becomes
        // (Some-value (select m k))
        FunctionApplication(
          selectors.toB((library.someType(to), 0)),
          Seq(ArraysEx.Select(toSMT(m), toSMT(k)))
        )

      case MapIsDefinedAt(m, k) =>
        val mt @ MapType(_, to) = m.getType
        declareSort(mt)
        // m.isDefinedAt(k) becomes
        // (is-Some (select m k))
        FunctionApplication(
          testers.toB(library.someType(to)),
          Seq(ArraysEx.Select(toSMT(m), toSMT(k)))
        )

      case MapUnion(m1, FiniteMap(elems, _, _)) =>
        val MapType(_, t) = m1.getType

        elems.foldLeft(toSMT(m1)) { case (m, (k,v)) =>
          ArraysEx.Store(m, toSMT(k), toSMT(CaseClass(library.someType(t), Seq(v))))
        }

      case p : Passes =>
        toSMT(matchToIfThenElse(p.asConstraint))

      case m : MatchExpr =>
        toSMT(matchToIfThenElse(m))


      case gv @ GenericValue(tpe, n) =>
        genericValues.cachedB(gv) {
          declareVariable(FreshIdentifier("gv"+n, tpe))
        }

      /**
       * ===== Everything else =====
       */
      case ap @ Application(caller, args) =>
        ArraysEx.Select(toSMT(caller), toSMT(tupleWrap(args)))

      case Not(u) => Core.Not(toSMT(u))
      case UMinus(u) => Ints.Neg(toSMT(u))
      case BVUMinus(u) => FixedSizeBitVectors.Neg(toSMT(u))
      case BVNot(u) => FixedSizeBitVectors.Not(toSMT(u))
      case Assert(a,_, b) => toSMT(IfExpr(a, b, Error(b.getType, "assertion failed")))

      case Equals(a,b) => Core.Equals(toSMT(a), toSMT(b))
      case Implies(a,b) => Core.Implies(toSMT(a), toSMT(b))
      case Plus(a,b) => Ints.Add(toSMT(a), toSMT(b))
      case Minus(a,b) => Ints.Sub(toSMT(a), toSMT(b))
      case Times(a,b) => Ints.Mul(toSMT(a), toSMT(b))
      case Division(a,b) => {
        val ar = toSMT(a)
        val br = toSMT(b)

        Core.ITE(
          Ints.GreaterEquals(ar, Ints.NumeralLit(0)),
          Ints.Div(ar, br),
          Ints.Neg(Ints.Div(Ints.Neg(ar), br)))
      }
      case Remainder(a,b) => {
        val q = toSMT(Division(a, b))
        Ints.Sub(toSMT(a), Ints.Mul(toSMT(b), q))
      }
      case Modulo(a,b) => {
        Ints.Mod(toSMT(a), toSMT(b))
      }
      case LessThan(a,b) => a.getType match {
        case Int32Type => FixedSizeBitVectors.SLessThan(toSMT(a), toSMT(b))
        case IntegerType => Ints.LessThan(toSMT(a), toSMT(b))
        case RealType => Reals.LessThan(toSMT(a), toSMT(b))
        case CharType => FixedSizeBitVectors.SLessThan(toSMT(a), toSMT(b))
      }
      case LessEquals(a,b) => a.getType match {
        case Int32Type => FixedSizeBitVectors.SLessEquals(toSMT(a), toSMT(b))
        case IntegerType => Ints.LessEquals(toSMT(a), toSMT(b))
        case RealType => Reals.LessEquals(toSMT(a), toSMT(b))
        case CharType => FixedSizeBitVectors.SLessEquals(toSMT(a), toSMT(b))
      }
      case GreaterThan(a,b) => a.getType match {
        case Int32Type => FixedSizeBitVectors.SGreaterThan(toSMT(a), toSMT(b))
        case IntegerType => Ints.GreaterThan(toSMT(a), toSMT(b))
        case RealType => Reals.GreaterThan(toSMT(a), toSMT(b))
        case CharType => FixedSizeBitVectors.SGreaterThan(toSMT(a), toSMT(b))
      }
      case GreaterEquals(a,b) => a.getType match {
        case Int32Type => FixedSizeBitVectors.SGreaterEquals(toSMT(a), toSMT(b))
        case IntegerType => Ints.GreaterEquals(toSMT(a), toSMT(b))
        case RealType => Reals.GreaterEquals(toSMT(a), toSMT(b))
        case CharType => FixedSizeBitVectors.SGreaterEquals(toSMT(a), toSMT(b))
      }
      case BVPlus(a,b) => FixedSizeBitVectors.Add(toSMT(a), toSMT(b))
      case BVMinus(a,b) => FixedSizeBitVectors.Sub(toSMT(a), toSMT(b))
      case BVTimes(a,b) => FixedSizeBitVectors.Mul(toSMT(a), toSMT(b))
      case BVDivision(a,b) => FixedSizeBitVectors.SDiv(toSMT(a), toSMT(b))
      case BVRemainder(a,b) => FixedSizeBitVectors.SRem(toSMT(a), toSMT(b))
      case BVAnd(a,b) => FixedSizeBitVectors.And(toSMT(a), toSMT(b))
      case BVOr(a,b) => FixedSizeBitVectors.Or(toSMT(a), toSMT(b))
      case BVXOr(a,b) => FixedSizeBitVectors.XOr(toSMT(a), toSMT(b))
      case BVShiftLeft(a,b) => FixedSizeBitVectors.ShiftLeft(toSMT(a), toSMT(b))
      case BVAShiftRight(a,b) => FixedSizeBitVectors.AShiftRight(toSMT(a), toSMT(b))
      case BVLShiftRight(a,b) => FixedSizeBitVectors.LShiftRight(toSMT(a), toSMT(b))

      case RealPlus(a,b) => Reals.Add(toSMT(a), toSMT(b))
      case RealMinus(a,b) => Reals.Sub(toSMT(a), toSMT(b))
      case RealTimes(a,b) => Reals.Mul(toSMT(a), toSMT(b))
      case RealDivision(a,b) => Reals.Div(toSMT(a), toSMT(b))

      case And(sub) => Core.And(sub.map(toSMT): _*)
      case Or(sub) => Core.Or(sub.map(toSMT): _*)
      case IfExpr(cond, thenn, elze) => Core.ITE(toSMT(cond), toSMT(thenn), toSMT(elze))
      case f@FunctionInvocation(_, sub) =>
        if (sub.isEmpty) declareFunction(f.tfd) else {
          FunctionApplication(
            declareFunction(f.tfd),
            sub.map(toSMT)
          )
        }
      case o =>
        unsupported(s"Tree ${o.asString}")
    }
  }

  /* Translate an SMTLIB term back to a Leon Expr */

  protected def fromSMT(pair: (Term, TypeTree))(implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): Expr = {
    fromSMT(pair._1, pair._2)
  }

  protected def fromSMT(s: Term, tpe: TypeTree)(implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): Expr = (s, tpe) match {
    case (_, UnitType) =>
      UnitLiteral()

    case (FixedSizeBitVectors.BitVectorConstant(n, b), CharType) if b == BigInt(32) =>
      CharLiteral(n.toInt.toChar)

    case (SHexadecimal(h), CharType) =>
      CharLiteral(h.toInt.toChar)

    case (SNumeral(n), IntegerType) =>
      InfiniteIntegerLiteral(n)

    case (SDecimal(d), RealType) =>
      RealLiteral(d)

    case (SNumeral(n), RealType) =>
      RealLiteral(BigDecimal(n))

    case (Core.True(), BooleanType)  => BooleanLiteral(true)
    case (Core.False(), BooleanType)  => BooleanLiteral(false)

    case (FixedSizeBitVectors.BitVectorConstant(n, b), Int32Type) if b == BigInt(32) => IntLiteral(n.toInt)
    case (SHexadecimal(hexa), Int32Type) => IntLiteral(hexa.toInt)

    case (SimpleSymbol(s), _: ClassType) if constructors.containsB(s) =>
      constructors.toA(s) match {
        case cct: CaseClassType =>
          CaseClass(cct, Nil)
        case t =>
          unsupported("woot? for a single constructor for non-case-object: "+t.asString)
      }

    case (SimpleSymbol(s), tpe) if lets contains s =>
      fromSMT(lets(s), tpe)

    case (SimpleSymbol(s), _) =>
      variables.getA(s).map(_.toVariable).getOrElse {
        unsupported("Unknown symbol: "+s)
      }

    case (FunctionApplication(SimpleSymbol(SSymbol("ite")), Seq(cond, thenn, elze)), t) =>
      IfExpr(
        fromSMT(cond, BooleanType),
        fromSMT(thenn, t),
        fromSMT(elze, t)
      )

    case (FunctionApplication(SimpleSymbol(s), args), tpe) if constructors.containsB(s) =>
      constructors.toA(s) match {
        case cct: CaseClassType =>
          val rargs = args.zip(cct.fields.map(_.getType)).map(fromSMT)
          CaseClass(cct, rargs)
        case tt: TupleType =>
          val rargs = args.zip(tt.bases).map(fromSMT)
          tupleWrap(rargs)

        case ArrayType(baseType) =>
          val IntLiteral(size)                 = fromSMT(args(0), Int32Type)
          val RawArrayValue(_, elems, default) = fromSMT(args(1), RawArrayType(Int32Type, baseType))

          if(size > 10) {
            val definedElements = elems.collect {
              case (IntLiteral(i), value) => (i, value)
            }
            finiteArray(definedElements, Some(default, IntLiteral(size)), baseType)

          } else {
            val entries = for (i <- 0 to size-1) yield elems.getOrElse(IntLiteral(i), default)

            finiteArray(entries, None, baseType)
          }

        case t =>
          unsupported("Woot? structural type that is non-structural: "+t)
      }

    // EK: Since we have no type information, we cannot do type-directed
    // extraction of defs, instead, we expand them in smt-world
    case (SMTLet(binding, bindings, body), tpe) =>
      val defsMap: Map[SSymbol, Term] = (binding +: bindings).map {
        case VarBinding(s, value) => (s, value)
      }.toMap

      fromSMT(body, tpe)(lets ++ defsMap, letDefs)

    case (FunctionApplication(SimpleSymbol(SSymbol(app)), args), tpe) => {
      app match {
        case "-" =>
          (args, tpe) match {
            case (List(a), IntegerType) => UMinus(fromSMT(a, IntegerType))
            case (List(a, b), IntegerType) => Minus(fromSMT(a, IntegerType), fromSMT(b, IntegerType))
            case (List(a), RealType) => RealUMinus(fromSMT(a, RealType))
            case (List(a, b), RealType) => RealMinus(fromSMT(a, RealType), fromSMT(b, RealType))
          }
        case "/" =>
          (args, tpe) match {
            case (List(a, b), RealType) => RealDivision(fromSMT(a, RealType), fromSMT(b, RealType))
          }

        case _ =>
          unsupported("Function "+app+" not handled in fromSMT: "+s)
      }
    }
    case (QualifiedIdentifier(id, sort), tpe) =>
      unsupported("Unhandled case in fromSMT: " + id +": "+sort +" ("+tpe+")")
    case _ =>
      unsupported("Unhandled case in fromSMT: " + (s, tpe))
  }


  /* Send a command to the solver */
  def sendCommand(cmd: Command, rawOut: Boolean = false): CommandResponse = {
    out foreach { o =>
      SMTPrinter.printCommand(cmd, o)
      o.write("\n")
      o.flush()
    }
    interpreter.eval(cmd) match {
      case err@ErrorResponse(msg) if !hasError && !interrupted && !rawOut =>
        reporter.warning(s"Unexpected error from $name solver: $msg")
        // Store that there was an error. Now all following check()
        // invocations will return None
        addError()
        err
      case res => res
    }
  }


  /* Public solver interface */

  def free() = {
    interpreter.free()
    context.interruptManager.unregisterForInterrupts(this)
    out foreach { _.close }
  }

  override def assertCnstr(expr: Expr): Unit = if(!hasError) {
    variablesOf(expr).foreach(declareVariable)
    try {
      val term = toSMT(expr)(Map())
      sendCommand(SMTAssert(term))
    } catch {
      case i : IllegalArgumentException =>
        // Store that there was an error. Now all following check()
        // invocations will return None
        addError()
    }
  }

  override def reset() = {
    sendCommand(Reset(), rawOut = true) match {
      case ErrorResponse(msg) =>
        reporter.warning(s"Failed to reset $name: $msg")
        throw new CantResetException(this)
      case _ =>
    }
  }

  override def check: Option[Boolean] = {
    if (hasError) None
    else sendCommand(CheckSat()) match {
      case CheckSatStatus(SatStatus)     => Some(true)
      case CheckSatStatus(UnsatStatus)   => Some(false)
      case CheckSatStatus(UnknownStatus) => None
      case e                             => None
    }
  }

  protected def getModel(filter: Identifier => Boolean): Map[Identifier, Expr] = {
    val syms = variables.aSet.filter(filter).toList.map(variables.aToB)
    if (syms.isEmpty) {
      Map()
    } else {
      val cmd: Command = GetValue(
        syms.head,
        syms.tail.map(s => QualifiedIdentifier(SMTIdentifier(s)))
      )

      sendCommand(cmd) match {
        case GetValueResponseSuccess(valuationPairs) =>

          valuationPairs.collect {
            case (SimpleSymbol(sym), value) if variables.containsB(sym) =>
              val id = variables.toA(sym)

              (id, fromSMT(value, id.getType)(Map(), Map()))
          }.toMap
        case _ =>
          Map() //FIXME improve this
      }
    }
  }

  override def getModel: Map[Identifier, Expr] = getModel( _ => true)

  override def push(): Unit = {
    constructors.push()
    selectors.push()
    testers.push()
    variables.push()
    genericValues.push()
    sorts.push()
    functions.push()
    errors.push()
    sendCommand(Push(1))
  }

  override def pop(): Unit = {
    constructors.pop()
    selectors.pop()
    testers.pop()
    variables.pop()
    genericValues.pop()
    sorts.pop()
    functions.pop()
    errors.pop()

    sendCommand(Pop(1))
  }

}

// Unique numbers
protected object VCNumbers {
  private var nexts = Map[String, Int]().withDefaultValue(0)
  def getNext(id: String) = {
    val n = nexts(id)+1
    nexts += id -> n
    n
  }
}
