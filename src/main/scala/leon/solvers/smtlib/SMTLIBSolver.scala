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
  ForAll => SMTForall,
  Exists => SMTExists,
  Identifier => SMTIdentifier,
  Let => SMTLet,
  _
}
import _root_.smtlib.parser.CommandsResponses.{Error => ErrorResponse, _}
import _root_.smtlib.theories._
import _root_.smtlib.{Interpreter => SMTInterpreter}


abstract class SMTLIBSolver(val context: LeonContext,
                            val program: Program)
  extends IncrementalSolver with Interruptible {


  /* Solver name */
  def targetName: String
  override def name: String = "smt-"+targetName

  /* Reporter */
  protected val reporter = context.reporter

  /* Interface with Interpreter */

  def interpreterOps(ctx: LeonContext): Seq[String]

  def getNewInterpreter(ctx: LeonContext): SMTInterpreter

  protected val interpreter = getNewInterpreter(context)


  /* Printing VCs */

  protected lazy val out: Option[java.io.FileWriter] = if (reporter.isDebugEnabled) Some {
    val file = context.files.headOption.map(_.getName).getOrElse("NA")
    val n    = VCNumbers.getNext(targetName+file)

    val dir = new java.io.File("vcs")

    if (!dir.isDirectory) {
      dir.mkdir
    }

    new java.io.FileWriter(s"vcs/$targetName-$file-$n.smt2", false)
  } else None


  /* Interruptible interface */

  protected var interrupted = false

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

  protected def id2sym(id: Identifier): SSymbol = SSymbol(id.name+"!"+id.globalId)

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

  /* A manager object for the Option type (since it is hard-coded for Maps) */
  protected object OptionManager {
    lazy val leonOption = program.library.Option.get
    lazy val leonSome = program.library.Some.get
    lazy val leonNone = program.library.None.get
    def leonOptionType(tp: TypeTree) = AbstractClassType(leonOption, Seq(tp))

    def mkLeonSome(e: Expr) = CaseClass(CaseClassType(leonSome, Seq(e.getType)), Seq(e))
    def mkLeonNone(tp: TypeTree) = CaseClass(CaseClassType(leonNone, Seq(tp)), Seq())

    def someTester(tp: TypeTree): SSymbol = {
      val someTp = CaseClassType(leonSome, Seq(tp))
      testers.getB(someTp) match {
        case Some(s) => s
        case None =>
          declareOptionSort(tp)
          someTester(tp)
      }
    }
    def someConstructor(tp: TypeTree): SSymbol = {
      val someTp = CaseClassType(leonSome, Seq(tp))
      constructors.getB(someTp) match {
        case Some(s) => s
        case None =>
          declareOptionSort(tp)
          someConstructor(tp)
      }
    }
    def someSelector(tp: TypeTree): SSymbol = {
      val someTp = CaseClassType(leonSome, Seq(tp))
      selectors.getB(someTp,0) match {
        case Some(s) => s
        case None =>
          declareOptionSort(tp)
          someSelector(tp)
      }
    }

    def inlinedOptionGet(t : Term, tp: TypeTree): Term = {
      FunctionApplication(SSymbol("ite"), Seq(
        FunctionApplication(someTester(tp), Seq(t)),
        FunctionApplication(someSelector(tp), Seq(t)),
        declareVariable(FreshIdentifier("error_value", tp))
      ))
    }

  }


  /* Helper functions */


  protected def normalizeType(t: TypeTree): TypeTree = t match {
    case ct: ClassType if ct.parent.isDefined => ct.parent.get
    case tt: TupleType => tupleTypeWrap(tt.bases.map(normalizeType))
    case _ =>   t
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

  // Corresponds to a smt map, not a leon/scala array
  // Should NEVER escape past SMT-world
  private[smtlib] case class RawArrayType(from: TypeTree, to: TypeTree) extends TypeTree

  // Corresponds to a raw array value, which is coerced to a Leon expr depending on target type (set/array)
  // Should NEVER escape past SMT-world
  private[smtlib] case class RawArrayValue(keyTpe: TypeTree, elems: Map[Expr, Expr], default: Expr) extends Expr {
    val getType = RawArrayType(keyTpe, default.getType)
  }

  protected def fromRawArray(r: RawArrayValue, tpe: TypeTree): Expr = tpe match {
    case SetType(base) =>
      if (r.default != BooleanLiteral(false)) {
        reporter.warning("Co-finite sets are not supported.")
        throw new IllegalArgumentException
      }
      require(r.keyTpe == base, s"Type error in solver model, expected $base, found ${r.keyTpe}")

      finiteSet(r.elems.keySet, base)

    case RawArrayType(from, to) =>
      r

    case ft @ FunctionType(from, to) =>
      finiteLambda(r.default, r.elems.toSeq, from)

    case MapType(from, to) =>
      // We expect a RawArrayValue with keys in from and values in Option[to],
      // with default value == None
      require(from == r.keyTpe && r.default == OptionManager.mkLeonNone(to))
      val elems = r.elems.flatMap {
        case (k, CaseClass(leonSome, Seq(x))) => Some(k -> x)
        case (k, _) => None
      }.toSeq
      finiteMap(elems, from, to)

    case _ =>
      unsupported("Unable to extract from raw array for "+tpe)
  }

  protected def unsupported(str: Any) = reporter.fatalError(s"Unsupported in smt-$targetName: $str")

  protected def declareSort(t: TypeTree): Sort = {
    val tpe = normalizeType(t)
    sorts.cachedB(tpe) {
      tpe match {
        case BooleanType => Core.BoolSort()
        case IntegerType => Ints.IntSort()
        case Int32Type => FixedSizeBitVectors.BitVectorSort(32)
        case CharType => FixedSizeBitVectors.BitVectorSort(32)

        case RawArrayType(from, to) =>
          Sort(SMTIdentifier(SSymbol("Array")), Seq(declareSort(from), declareSort(to)))

        case MapType(from, to) =>
          declareMapSort(from, to)

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

  protected def declareOptionSort(of: TypeTree): Sort = {
    declareSort(OptionManager.leonOptionType(of))
  }

  protected def declareMapSort(from: TypeTree, to: TypeTree): Sort = {
    sorts.cachedB(MapType(from, to)) {
      val m = freshSym("Map")

      val toSort = declareOptionSort(to)
      val fromSort = declareSort(from)

      val arraySort = Sort(SMTIdentifier(SSymbol("Array")),
        Seq(fromSort, toSort))
      val cmd = DefineSort(m, Seq(), arraySort)

      sendCommand(cmd)
      Sort(SMTIdentifier(m), Seq())
    }
  }

  protected def getHierarchy(ct: ClassType): (ClassType, Seq[CaseClassType]) = ct match {
    case act: AbstractClassType =>
      (act, act.knownCCDescendents)
    case cct: CaseClassType =>
      cct.parent match {
        case Some(p) =>
          getHierarchy(p)
        case None =>
          (cct, List(cct))
      }
  }

  protected case class DataType(sym: SSymbol, cases: Seq[Constructor])
  protected case class Constructor(sym: SSymbol, tpe: TypeTree, fields: Seq[(SSymbol, TypeTree)])

  protected def findDependencies(t: TypeTree, dts: Map[TypeTree, DataType] = Map()): Map[TypeTree, DataType] = t match {
    case ct: ClassType =>
      val (root, sub) = getHierarchy(ct)

      if (!(dts contains root) && !(sorts containsA root)) {
        val sym = freshSym(ct.id)

        val conss = sub.map { case cct =>
          Constructor(freshSym(cct.id), cct, cct.fields.map(vd => (freshSym(vd.id), vd.getType)))
        }

        var cdts = dts + (root -> DataType(sym, conss))

        // look for dependencies
        for (ct <- root +: sub; f <- ct.fields) {
          cdts ++= findDependencies(f.getType, cdts)
        }

        cdts
      } else {
        dts
      }

    case tt @ TupleType(bases) =>
      if (!(dts contains t) && !(sorts containsA t)) {
        val sym = freshSym("tuple"+bases.size)

        val c = Constructor(freshSym(sym.name), tt, bases.zipWithIndex.map {
          case (tpe, i) => (freshSym("_"+(i+1)), tpe)
        })

        var cdts = dts + (tt -> DataType(sym, Seq(c)))

        for (b <- bases) {
          cdts ++= findDependencies(b, cdts)
        }
        cdts
      } else {
        dts
      }

    case UnitType =>
      if (!(dts contains t) && !(sorts containsA t)) {

        val sym = freshSym("Unit")

        dts + (t -> DataType(sym, Seq(Constructor(freshSym(sym.name), t, Nil))))
      } else {
        dts
      }

    case at @ ArrayType(base) =>
      if (!(dts contains t) && !(sorts containsA t)) {
        val sym = freshSym("array")

        val c = Constructor(freshSym(sym.name), at, List(
          (freshSym("size"), Int32Type),
          (freshSym("content"), RawArrayType(Int32Type, base))
        ))

        val cdts = dts + (at -> DataType(sym, Seq(c)))

        findDependencies(base, cdts)
      } else {
        dts
      }

    case _ =>
      dts
  }

  protected def declareDatatypes(datatypes: Map[TypeTree, DataType]): Unit = {
    // We pre-declare ADTs
    for ((tpe, DataType(sym, _)) <- datatypes) {
      sorts += tpe -> Sort(SMTIdentifier(sym))
    }

    def toDecl(c: Constructor): SMTConstructor = {
      val s = c.sym

      testers += c.tpe -> SSymbol("is-"+s.name)
      constructors += c.tpe -> s

      SMTConstructor(s, c.fields.zipWithIndex.map {
        case ((cs, t), i) =>
          selectors += (c.tpe, i) -> cs
          (cs, declareSort(t))
      })
    }

    val adts = for ((tpe, DataType(sym, cases)) <- datatypes.toList) yield {
      (sym, cases.map(toDecl))
    }


    val cmd = DeclareDatatypes(adts)
    sendCommand(cmd)
  }

  protected def declareStructuralSort(t: TypeTree): Sort = {
    // Populates the dependencies of the structural type to define.
    val datatypes = findDependencies(t)

    declareDatatypes(datatypes)

    sorts.toB(t)
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

  protected def declareMapUnion(from: TypeTree, to: TypeTree): SSymbol = {
    // FIXME cache results
    val a = declareSort(from)
    val b = declareSort(OptionManager.leonOptionType(to))
    val arraySort = Sort(SMTIdentifier(SSymbol("Array")), Seq(a, b))

    val f = freshSym("map_union")

    sendCommand(DeclareFun(f, Seq(arraySort, arraySort), arraySort))

    val v  = SSymbol("v")
    val a1 = SSymbol("a1")
    val a2 = SSymbol("a2")

    val axiom = SMTForall(
      SortedVar(a1, arraySort), Seq(SortedVar(a2, arraySort), SortedVar(v,a)),
      Core.Equals(
        ArraysEx.Select(
          FunctionApplication(f: QualifiedIdentifier, Seq(a1: Term, a2: Term)),
          v: Term
        ),
        Core.ITE(
          FunctionApplication(
            OptionManager.someTester(to),
            Seq(ArraysEx.Select(a2: Term, v: Term))
          ),
          ArraysEx.Select(a2,v),
          ArraysEx.Select(a1,v)
        )
      )
    )

    sendCommand(SMTAssert(axiom))
    f
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

      case InfiniteIntegerLiteral(i) => if (i > 0) Ints.NumeralLit(i) else Ints.Neg(Ints.NumeralLit(-i))
      case IntLiteral(i) => FixedSizeBitVectors.BitVectorLit(Hexadecimal.fromInt(i))
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

      case CaseClassInstanceOf(cct, e) =>
        declareSort(cct)
        val tester = testers.toB(cct)
        FunctionApplication(tester, Seq(toSMT(e)))

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

      /**
       * ===== Map operations =====
       */
      case m @ FiniteMap(elems) =>
        import OptionManager._
        val mt @ MapType(_, to) = m.getType
        val ms = declareSort(mt)

        var res: Term = FunctionApplication(
          QualifiedIdentifier(SMTIdentifier(SSymbol("const")), Some(ms)),
          List(toSMT(mkLeonNone(to)))
        )
        for ((k, v) <- elems) {
          res = ArraysEx.Store(res, toSMT(k), toSMT(mkLeonSome(v)))
        }

        res

      case MapGet(m, k) =>
        import OptionManager._
        val mt@MapType(_, vt) = m.getType
        declareSort(mt)
        // m(k) becomes
        // (Option$get (select m k))
        inlinedOptionGet(ArraysEx.Select(toSMT(m), toSMT(k)), vt)

      case MapIsDefinedAt(m, k) =>
        import OptionManager._
        val mt@MapType(_, vt) = m.getType
        declareSort(mt)
        // m.isDefinedAt(k) becomes
        // (Option$isDefined (select m k))
        FunctionApplication(
          someTester(vt),
          Seq(ArraysEx.Select(toSMT(m), toSMT(k)))
        )

      case MapUnion(m1, m2) =>
        val MapType(vk, vt) = m1.getType
        FunctionApplication(
          declareMapUnion(vk, vt),
          Seq(toSMT(m1), toSMT(m2))
        )

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
      case Modulo(a,b) => {
        val q = toSMT(Division(a, b))
        Ints.Sub(toSMT(a), Ints.Mul(toSMT(b), q))
      }
      case LessThan(a,b) => a.getType match {
        case Int32Type => FixedSizeBitVectors.SLessThan(toSMT(a), toSMT(b))
        case IntegerType => Ints.LessThan(toSMT(a), toSMT(b))
      }
      case LessEquals(a,b) => a.getType match {
        case Int32Type => FixedSizeBitVectors.SLessEquals(toSMT(a), toSMT(b))
        case IntegerType => Ints.LessEquals(toSMT(a), toSMT(b))
      }
      case GreaterThan(a,b) => a.getType match {
        case Int32Type => FixedSizeBitVectors.SGreaterThan(toSMT(a), toSMT(b))
        case IntegerType => Ints.GreaterThan(toSMT(a), toSMT(b))
      }
      case GreaterEquals(a,b) => a.getType match {
        case Int32Type => FixedSizeBitVectors.SGreaterEquals(toSMT(a), toSMT(b))
        case IntegerType => Ints.GreaterEquals(toSMT(a), toSMT(b))
      }
      case BVPlus(a,b) => FixedSizeBitVectors.Add(toSMT(a), toSMT(b))
      case BVMinus(a,b) => FixedSizeBitVectors.Sub(toSMT(a), toSMT(b))
      case BVTimes(a,b) => FixedSizeBitVectors.Mul(toSMT(a), toSMT(b))
      case BVDivision(a,b) => FixedSizeBitVectors.SDiv(toSMT(a), toSMT(b))
      case BVModulo(a,b) => FixedSizeBitVectors.SRem(toSMT(a), toSMT(b))
      case BVAnd(a,b) => FixedSizeBitVectors.And(toSMT(a), toSMT(b))
      case BVOr(a,b) => FixedSizeBitVectors.Or(toSMT(a), toSMT(b))
      case BVXOr(a,b) => FixedSizeBitVectors.XOr(toSMT(a), toSMT(b))
      case BVShiftLeft(a,b) => FixedSizeBitVectors.ShiftLeft(toSMT(a), toSMT(b))
      case BVAShiftRight(a,b) => FixedSizeBitVectors.AShiftRight(toSMT(a), toSMT(b))
      case BVLShiftRight(a,b) => FixedSizeBitVectors.LShiftRight(toSMT(a), toSMT(b))
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
        reporter.warning(s"Unsupported Tree in smt-$targetName: $o")
        throw new IllegalArgumentException
    }
  }

  /* Translate an SMTLIB term back to a Leon Expr */

  protected def fromSMT(pair: (Term, TypeTree))(implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): Expr = {
    fromSMT(pair._1, pair._2)
  }

  protected def fromSMT(s: Term, tpe: TypeTree)(implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): Expr = (s, tpe) match {
    case (_, UnitType) =>
      UnitLiteral()

    case (SHexadecimal(h), CharType) =>
      CharLiteral(h.toInt.toChar)

    case (SNumeral(n), IntegerType) =>
      InfiniteIntegerLiteral(n)

    case (Core.True(), BooleanType)  => BooleanLiteral(true)
    case (Core.False(), BooleanType)  => BooleanLiteral(false)

    case (FixedSizeBitVectors.BitVectorConstant(n, b), Int32Type) if b == BigInt(32) => IntLiteral(n.toInt)
    case (SHexadecimal(hexa), Int32Type) => IntLiteral(hexa.toInt)

    case (SimpleSymbol(s), _: ClassType) if constructors.containsB(s) =>
      constructors.toA(s) match {
        case cct: CaseClassType =>
          CaseClass(cct, Nil)
        case t =>
          unsupported("woot? for a single constructor for non-case-object: "+t)
      }

    case (SimpleSymbol(s), tpe) if lets contains s =>
      fromSMT(lets(s), tpe)

    case (SimpleSymbol(s), _) =>
      variables.getA(s).map(_.toVariable).getOrElse {
        unsupported("Unknown symbol: "+s)
      }

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
          args match {
            case List(a) => UMinus(fromSMT(a, IntegerType))
            case List(a, b) => Minus(fromSMT(a, IntegerType), fromSMT(b, IntegerType))
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
  def sendCommand(cmd: Command): CommandResponse = {
    out foreach { o =>
      SMTPrinter.printCommand(cmd, o)
      o.write("\n")
      o.flush()
    }
    interpreter.eval(cmd) match {
      case err@ErrorResponse(msg) if !hasError && !interrupted =>
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

  override def check: Option[Boolean] = {
    if (hasError) None
    else sendCommand(CheckSat()) match {
      case CheckSatStatus(SatStatus)     => Some(true)
      case CheckSatStatus(UnsatStatus)   => Some(false)
      case CheckSatStatus(UnknownStatus) => None
      case e                             => None
    }
  }

  override def getModel: Map[Identifier, Expr] = {
    val syms = variables.bSet.toList
    if (syms.isEmpty) {
      Map()
    } else {
      val cmd: Command =
        GetValue(syms.head,
          syms.tail.map(s => QualifiedIdentifier(SMTIdentifier(s)))
        )


      val GetValueResponseSuccess(valuationPairs) = sendCommand(cmd)

      valuationPairs.collect {
        case (SimpleSymbol(sym), value) if variables.containsB(sym) =>
          val id = variables.toA(sym)

          (id, fromSMT(value, id.getType)(Map(), Map()))
      }.toMap
    }
  }

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

  override def pop(lvl: Int = 1): Unit = {
    assert(lvl == 1, "Current implementation only supports lvl = 1")

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
