/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers
package smtlib

import utils._

import purescala.Common._
import purescala.Expressions._
import purescala.Extractors._
import purescala.ExprOps._
import purescala.Types._
import purescala.TypeOps._
import purescala.Constructors._
import purescala.Definitions._

import _root_.smtlib.common._
import _root_.smtlib.printer.{ RecursivePrinter => SMTPrinter }
import _root_.smtlib.parser.Commands.{
  Constructor => SMTConstructor,
  FunDef => SMTFunDef,
  Assert => _,
  _
}
import _root_.smtlib.parser.Terms.{
  Forall => SMTForall,
  Exists => SMTExists,
  Identifier => SMTIdentifier,
  Let => SMTLet,
  _
}
import _root_.smtlib.parser.CommandsResponses.{ Error => ErrorResponse, _ }
import _root_.smtlib.theories.{Constructors => SmtLibConstructors, _}
import _root_.smtlib.interpreters.ProcessInterpreter

trait SMTLIBTarget extends Interruptible {
  val context: LeonContext
  val program: Program

  def targetName: String

  implicit val debugSection: DebugSection

  protected def interpreterOps(ctx: LeonContext): Seq[String]

  protected def getNewInterpreter(ctx: LeonContext): ProcessInterpreter

  protected def unsupported(t: Tree, str: String): Nothing

  protected lazy val interpreter = getNewInterpreter(context)

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

  def free() = {
    interpreter.free()
    context.interruptManager.unregisterForInterrupts(this)
    debugOut foreach { _.close }
  }

  /* Printing VCs */
  protected lazy val debugOut: Option[java.io.FileWriter] = {
    if (context.reporter.isDebugEnabled) {
      val file = context.files.headOption.map(_.getName).getOrElse("NA")
      val n = DebugFileNumbers.next(targetName + file)

      val fileName = s"smt-sessions/$targetName-$file-$n.smt2"

      val javaFile = new java.io.File(fileName)
      javaFile.getParentFile.mkdirs()

      context.reporter.debug(s"Outputting smt session into $fileName")

      val fw = new java.io.FileWriter(javaFile, false)

      fw.write("; Options: " + interpreterOps(context).mkString(" ") + "\n")

      Some(fw)
    } else {
      None
    }
  }

  /* Send a command to the solver */
  def emit(cmd: SExpr, rawOut: Boolean = false): SExpr = {
    debugOut foreach { o =>
      SMTPrinter.printSExpr(cmd, o)
      o.write("\n")
      o.flush()
    }
    interpreter.eval(cmd) match {
      case err @ ErrorResponse(msg) if !hasError && !interrupted && !rawOut =>
        context.reporter.warning(s"Unexpected error from $targetName solver: $msg")
        //println(Thread.currentThread().getStackTrace.map(_.toString).take(10).mkString("\n"))
        // Store that there was an error. Now all following check()
        // invocations will return None
        addError()
        err
      case res =>
        res
    }
  }

  def parseSuccess() = {
    val res = interpreter.parser.parseGenResponse
    if (res != Success) {
      context.reporter.warning("Unnexpected result from " + targetName + ": " + res + " expected success")
    }
  }

  /*
   * Translation from Leon Expressions to SMTLIB terms and reverse
   */

  /* Symbol handling */
  protected object SimpleSymbol {
    def apply(sym: SSymbol) = QualifiedIdentifier(SMTIdentifier(sym))
    def unapply(term: Term): Option[SSymbol] = term match {
      case QualifiedIdentifier(SMTIdentifier(sym, Seq()), None) => Some(sym)
      case _ => None
    }
  }

  import scala.language.implicitConversions
  protected implicit def symbolToQualifiedId(s: SSymbol): QualifiedIdentifier = SimpleSymbol(s)

  protected val adtManager = new ADTManager(context)

  protected val library = program.library

  protected def id2sym(id: Identifier): SSymbol = {
    SSymbol(id.uniqueNameDelimited("!").replace("|", "$pipe").replace("\\", "$backslash"))
  }

  protected def freshSym(id: Identifier): SSymbol = freshSym(id.name)
  protected def freshSym(name: String): SSymbol = id2sym(FreshIdentifier(name))

  /* Metadata for CC, and variables */
  protected val constructors  = new IncrementalBijection[TypeTree, SSymbol]()
  protected val selectors     = new IncrementalBijection[(TypeTree, Int), SSymbol]()
  protected val testers       = new IncrementalBijection[TypeTree, SSymbol]()
  protected val variables     = new IncrementalBijection[Identifier, SSymbol]()
  protected val sorts         = new IncrementalBijection[TypeTree, Sort]()
  protected val functions     = new IncrementalBijection[TypedFunDef, SSymbol]()
  protected val lambdas       = new IncrementalBijection[FunctionType, SSymbol]()
  protected val errors        = new IncrementalBijection[Unit, Boolean]()
  protected def hasError = errors.getB(()) contains true
  protected def addError() = errors += () -> true

  /* Helper functions */

  protected def normalizeType(t: TypeTree): TypeTree = t match {
    case ct: ClassType => ct.root
    case tt: TupleType => tupleTypeWrap(tt.bases.map(normalizeType))
    case _             => t
  }

  protected def quantifiedTerm(
    quantifier: (SortedVar, Seq[SortedVar], Term) => Term,
    vars: Seq[Identifier],
    body: Expr)(
      implicit bindings: Map[Identifier, Term]): Term = {
    if (vars.isEmpty) toSMT(body)
    if (vars.isEmpty) toSMT(body)(Map())
    else {
      val sortedVars = vars map { id =>
        SortedVar(id2sym(id), declareSort(id.getType))
      }
      quantifier(
        sortedVars.head,
        sortedVars.tail,
        toSMT(body)(bindings ++ vars.map { id => id -> (id2sym(id): Term) }.toMap))
    }
  }

  // Returns a quantified term where all free variables in the body have been quantified
  protected def quantifiedTerm(quantifier: (SortedVar, Seq[SortedVar], Term) => Term, body: Expr)(
    implicit bindings: Map[Identifier, Term]): Term =
    quantifiedTerm(quantifier, variablesOf(body).toSeq, body)

  protected def fromRawArray(r: RawArrayValue, tpe: TypeTree): Expr = tpe match {
    case SetType(base) =>
      if (r.default != BooleanLiteral(false)) {
        unsupported(r, "Solver returned a co-finite set which is not supported.")
      }
      require(r.keyTpe == base, s"Type error in solver model, expected $base, found ${r.keyTpe}")
      FiniteSet(r.elems.keySet, base)

    case BagType(base) =>
      if (r.default != InfiniteIntegerLiteral(0)) {
        unsupported(r, "Solver returned an infinite bag which is not supported.")
      }
      require(r.keyTpe == base, s"Type error in solver model, expected $base, found ${r.keyTpe}")
      FiniteBag(r.elems, base)

    case RawArrayType(from, to) =>
      r

    case ft @ FunctionType(from, to) =>
      val elems = r.elems.toSeq.map { case (k, v) => unwrapTuple(k, from.size) -> v }
      FiniteLambda(elems, r.default, ft)

    case MapType(from, to) =>
      // We expect a RawArrayValue with keys in from and values in Option[to],
      // with default value == None
      if (r.default.getType != library.noneType(to)) {
        unsupported(r, "Solver returned a co-finite map which is not supported.")
      }
      require(r.keyTpe == from, s"Type error in solver model, expected $from, found ${r.keyTpe}")

      val elems = r.elems.flatMap {
        case (k, CaseClass(leonSome, Seq(x))) => Some(k -> x)
        case (k, _)                           => None
      }.toMap
      FiniteMap(elems, from, to)

    case other =>
      unsupported(other, "Unable to extract from raw array for " + tpe)
  }

  protected def declareSort(t: TypeTree): Sort = {
    val tpe = normalizeType(t)
    sorts.cachedB(tpe) {
      tpe match {
        case BooleanType => Core.BoolSort()
        case IntegerType => Ints.IntSort()
        case RealType    => Reals.RealSort()
        case Int8Type    => FixedSizeBitVectors.BitVectorSort(8)
        case Int32Type   => FixedSizeBitVectors.BitVectorSort(32)
        case CharType    => FixedSizeBitVectors.BitVectorSort(32)

        case RawArrayType(from, to) =>
          Sort(SMTIdentifier(SSymbol("Array")), Seq(declareSort(from), declareSort(to)))

        case MapType(from, to) =>
          declareSort(RawArrayType(from, library.optionType(to)))

        case FunctionType(from, to) =>
          Ints.IntSort()

        case _: ClassType | _: TupleType | _: ArrayType | _: TypeParameter | UnitType =>
          declareStructuralSort(tpe)

        case other =>
          unsupported(other, s"Could not transform $other into an SMT sort")
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

      testers += c.tpe -> SSymbol("is-" + s.name)
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
      emit(cmd)
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
      emit(cmd)
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
      emit(DeclareFun(
        s,
        tfd.params.map((p: ValDef) => declareSort(p.getType)),
        declareSort(tfd.returnType)))
      s
    }
  }

  protected def declareLambda(tpe: FunctionType): SSymbol = {
    val realTpe = bestRealType(tpe).asInstanceOf[FunctionType]
    lambdas.cachedB(realTpe) {
      val id = FreshIdentifier("dynLambda")
      val s = id2sym(id)
      emit(DeclareFun(
        s,
        (realTpe +: realTpe.from).map(declareSort),
        declareSort(realTpe.to)
      ))
      s
    }
  }

  /* Translate a Leon Expr to an SMTLIB term */

  def sortToSMT(s: Sort): SExpr = {
    s match {
      case Sort(id, Nil) =>
        id.symbol

      case Sort(id, subs) =>
        SList((id.symbol +: subs.map(sortToSMT)).toList)
    }
  }

  protected def toSMT(t: TypeTree): SExpr = {
    sortToSMT(declareSort(t))
  }

  protected def toSMT(e: Expr)(implicit bindings: Map[Identifier, Term]): Term = {
    e match {
      case Variable(id) =>
        declareSort(e.getType)
        bindings.getOrElse(id, variables.toB(id))

      case UnitLiteral() =>
        declareSort(UnitType)

        declareVariable(FreshIdentifier("Unit", UnitType))

      case InfiniteIntegerLiteral(i) => if (i >= 0) Ints.NumeralLit(i) else Ints.Neg(Ints.NumeralLit(-i))
      case ByteLiteral(b)            => FixedSizeBitVectors.BitVectorLit(Hexadecimal.fromString(toByteHex(b)).get)
      case IntLiteral(i)             => FixedSizeBitVectors.BitVectorLit(Hexadecimal.fromInt(i))
      case FractionalLiteral(n, d)   => Reals.Div(Reals.NumeralLit(n), Reals.NumeralLit(d))
      case CharLiteral(c)            => FixedSizeBitVectors.BitVectorLit(Hexadecimal.fromInt(c.toInt))
      case BooleanLiteral(v)         => Core.BoolConst(v)
      case Let(b, d, e) =>
        val id = id2sym(b)
        val value = toSMT(d)
        val newBody = toSMT(e)(bindings + (b -> id))

        SMTLet(
          VarBinding(id, value),
          Seq(),
          newBody)

      case er @ Error(tpe, _) =>
        declareVariable(FreshIdentifier("error_value", tpe))

      case s @ CaseClassSelector(cct, e, id) =>
        declareSort(cct)
        val selector = selectors.toB((cct, s.selectorIndex))
        FunctionApplication(selector, Seq(toSMT(e)))

      case AsInstanceOf(expr, cct) =>
        toSMT(expr)

      case IsInstanceOf(e, cct) =>
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
              SmtLibConstructors.or(oneOf.map(FunctionApplication(_, Seq(es: Term)))))
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
        val selector = selectors.toB((tpe, i - 1))
        FunctionApplication(selector, Seq(toSMT(t)))

      case al @ RawArraySelect(a, i) =>
        ArraysEx.Select(toSMT(a), toSMT(i))
      case al @ RawArrayUpdated(a, i, e) =>
        ArraysEx.Store(toSMT(a), toSMT(i), toSMT(e))
      case ra @ RawArrayValue(keyTpe, elems, default) =>
        val s = declareSort(ra.getType)

        var res: Term = FunctionApplication(
          QualifiedIdentifier(SMTIdentifier(SSymbol("const")), Some(s)),
          List(toSMT(default)))
        for ((k, v) <- elems) {
          res = ArraysEx.Store(res, toSMT(k), toSMT(v))
        }

        res

      /**
       * ===== Map operations =====
       */
      case m @ FiniteMap(elems, _, _) =>
        val mt @ MapType(from, to) = m.getType
        declareSort(mt)

        toSMT(RawArrayValue(from, elems.map {
          case (k, v) => k -> CaseClass(library.someType(to), Seq(v))
        }.toMap, CaseClass(library.noneType(to), Seq())))

      case MapApply(m, k) =>
        val mt @ MapType(_, to) = m.getType
        declareSort(mt)
        // m(k) becomes
        // (Some-value (select m k))
        FunctionApplication(
          selectors.toB((library.someType(to), 0)),
          Seq(ArraysEx.Select(toSMT(m), toSMT(k))))

      case MapIsDefinedAt(m, k) =>
        val mt @ MapType(_, to) = m.getType
        declareSort(mt)
        // m.isDefinedAt(k) becomes
        // (is-Some (select m k))
        FunctionApplication(
          testers.toB(library.someType(to)),
          Seq(ArraysEx.Select(toSMT(m), toSMT(k))))

      case MapUnion(m1, FiniteMap(elems, _, _)) =>
        val MapType(_, t) = m1.getType

        elems.foldLeft(toSMT(m1)) {
          case (m, (k, v)) =>
            ArraysEx.Store(m, toSMT(k), toSMT(CaseClass(library.someType(t), Seq(v))))
        }

      case p: Passes =>
        toSMT(matchToIfThenElse(p.asConstraint))

      case m: MatchExpr =>
        toSMT(matchToIfThenElse(m))

      case gv @ GenericValue(tpe, n) =>
        declareSort(tpe)
        val constructor = constructors.toB(tpe)
        FunctionApplication(constructor, Seq(toSMT(InfiniteIntegerLiteral(n))))

      case synthesis.utils.MutableExpr(ex) =>
        toSMT(ex)

      /**
       * ===== Everything else =====
       */
      case ap @ Application(caller, args) =>
        val dyn = declareLambda(caller.getType.asInstanceOf[FunctionType])
        FunctionApplication(dyn, (caller +: args).map(toSMT))

      case Not(u)          => Core.Not(toSMT(u))
      case UMinus(u)       => Ints.Neg(toSMT(u))
      case BVUMinus(u)     => FixedSizeBitVectors.Neg(toSMT(u))
      case BVNot(u)        => FixedSizeBitVectors.Not(toSMT(u))
      case Assert(a, _, b) => toSMT(IfExpr(a, b, Error(b.getType, "assertion failed")))

      case Equals(a, b)    => Core.Equals(toSMT(a), toSMT(b))
      case Implies(a, b)   => Core.Implies(toSMT(a), toSMT(b))
      case Plus(a, b)      => Ints.Add(toSMT(a), toSMT(b))
      case Minus(a, b)     => Ints.Sub(toSMT(a), toSMT(b))
      case Times(a, b)     => Ints.Mul(toSMT(a), toSMT(b))
      case Division(a, b) => {
        val ar = toSMT(a)
        val br = toSMT(b)

        Core.ITE(
          Ints.GreaterEquals(ar, Ints.NumeralLit(0)),
          Ints.Div(ar, br),
          Ints.Neg(Ints.Div(Ints.Neg(ar), br)))
      }
      case Remainder(a, b) => {
        val q = toSMT(Division(a, b))
        Ints.Sub(toSMT(a), Ints.Mul(toSMT(b), q))
      }
      case Modulo(a, b) => {
        Ints.Mod(toSMT(a), toSMT(b))
      }
      case LessThan(a, b) => a.getType match {
        case Int32Type   => FixedSizeBitVectors.SLessThan(toSMT(a), toSMT(b))
        case IntegerType => Ints.LessThan(toSMT(a), toSMT(b))
        case RealType    => Reals.LessThan(toSMT(a), toSMT(b))
        case CharType    => FixedSizeBitVectors.SLessThan(toSMT(a), toSMT(b))
      }
      case LessEquals(a, b) => a.getType match {
        case Int32Type   => FixedSizeBitVectors.SLessEquals(toSMT(a), toSMT(b))
        case IntegerType => Ints.LessEquals(toSMT(a), toSMT(b))
        case RealType    => Reals.LessEquals(toSMT(a), toSMT(b))
        case CharType    => FixedSizeBitVectors.SLessEquals(toSMT(a), toSMT(b))
      }
      case GreaterThan(a, b) => a.getType match {
        case Int32Type   => FixedSizeBitVectors.SGreaterThan(toSMT(a), toSMT(b))
        case IntegerType => Ints.GreaterThan(toSMT(a), toSMT(b))
        case RealType    => Reals.GreaterThan(toSMT(a), toSMT(b))
        case CharType    => FixedSizeBitVectors.SGreaterThan(toSMT(a), toSMT(b))
      }
      case GreaterEquals(a, b) => a.getType match {
        case Int32Type   => FixedSizeBitVectors.SGreaterEquals(toSMT(a), toSMT(b))
        case IntegerType => Ints.GreaterEquals(toSMT(a), toSMT(b))
        case RealType    => Reals.GreaterEquals(toSMT(a), toSMT(b))
        case CharType    => FixedSizeBitVectors.SGreaterEquals(toSMT(a), toSMT(b))
      }
      case BVPlus(a, b)              => FixedSizeBitVectors.Add(toSMT(a), toSMT(b))
      case BVMinus(a, b)             => FixedSizeBitVectors.Sub(toSMT(a), toSMT(b))
      case BVTimes(a, b)             => FixedSizeBitVectors.Mul(toSMT(a), toSMT(b))
      case BVDivision(a, b)          => FixedSizeBitVectors.SDiv(toSMT(a), toSMT(b))
      case BVRemainder(a, b)         => FixedSizeBitVectors.SRem(toSMT(a), toSMT(b))
      case BVAnd(a, b)               => FixedSizeBitVectors.And(toSMT(a), toSMT(b))
      case BVOr(a, b)                => FixedSizeBitVectors.Or(toSMT(a), toSMT(b))
      case BVXOr(a, b)               => FixedSizeBitVectors.XOr(toSMT(a), toSMT(b))
      case BVShiftLeft(a, b)         => FixedSizeBitVectors.ShiftLeft(toSMT(a), toSMT(b))
      case BVAShiftRight(a, b)       => FixedSizeBitVectors.AShiftRight(toSMT(a), toSMT(b))
      case BVLShiftRight(a, b)       => FixedSizeBitVectors.LShiftRight(toSMT(a), toSMT(b))
      case c @ BVWideningCast(e, _)  => FixedSizeBitVectors.SignExtend(c.to - c.from, toSMT(e))
      case c @ BVNarrowingCast(e, _) => FixedSizeBitVectors.Extract(c.to - 1, 0, toSMT(e))

      case RealPlus(a, b)            => Reals.Add(toSMT(a), toSMT(b))
      case RealMinus(a, b)           => Reals.Sub(toSMT(a), toSMT(b))
      case RealTimes(a, b)           => Reals.Mul(toSMT(a), toSMT(b))
      case RealDivision(a, b)        => Reals.Div(toSMT(a), toSMT(b))
      case RealUMinus(a)             => Reals.Neg(toSMT(a))

      case And(sub)                  => SmtLibConstructors.and(sub.map(toSMT))
      case Or(sub)                   => SmtLibConstructors.or(sub.map(toSMT))
      case IfExpr(cond, thenn, elze) => Core.ITE(toSMT(cond), toSMT(thenn), toSMT(elze))
      case f @ FunctionInvocation(_, sub) =>
        if (sub.isEmpty) declareFunction(f.tfd) else {
          FunctionApplication(
            declareFunction(f.tfd),
            sub.map(toSMT))
        }
      case Forall(vs, bd) =>
        quantifiedTerm(SMTForall, vs map { _.id }, bd)(Map())

      case ArrayForall(array, from, to, pred) =>
        val tpe @ ArrayType(base) = normalizeType(array.getType)

        val index = FreshIdentifier("i", Int32Type)
        declareVariable(index)

        val Lambda(Seq(ValDef(el)), predBody) = pred
        val substBody = replaceFromIDs(Map(el -> ArraySelect(array, index.toVariable)), predBody)
        val rSubstBody = toSMT(substBody)

        SMTForall(
          SortedVar(id2sym(index), declareSort(Int32Type)), Seq(),
          Core.Implies(
            Core.And(
              FixedSizeBitVectors.SGreaterEquals(id2sym(index), toSMT(from)),
              FixedSizeBitVectors.SLessThan(id2sym(index), toSMT(to))),
            rSubstBody
          )
        )
      case ArrayExists(array, from, to, pred) =>
        val tpe @ ArrayType(base) = normalizeType(array.getType)

        val index = FreshIdentifier("i", Int32Type)
        declareVariable(index)

        val Lambda(Seq(ValDef(el)), predBody) = pred
        val substBody = replaceFromIDs(Map(el -> ArraySelect(array, index.toVariable)), predBody)
        val rSubstBody = toSMT(substBody)

        SMTExists(
          SortedVar(id2sym(index), declareSort(Int32Type)), Seq(),
          Core.And(
            FixedSizeBitVectors.SGreaterEquals(id2sym(index), toSMT(from)),
            FixedSizeBitVectors.SLessThan(id2sym(index), toSMT(to)),
            rSubstBody
          )
        )


      case BoundedForall(from, to, pred) =>
        val intType = from.getType
        val index = FreshIdentifier("i", intType)
        declareVariable(index)

        val Lambda(Seq(ValDef(el)), predBody) = pred
        val substBody = replaceFromIDs(Map(el -> index.toVariable), predBody)
        val rSubstBody = toSMT(substBody)

        SMTForall(
          SortedVar(id2sym(index), declareSort(intType)), Seq(),
          Core.Implies(
            Core.And(
              (if(intType == Int32Type)
                FixedSizeBitVectors.SGreaterEquals(id2sym(index), toSMT(from))
              else
                Ints.GreaterEquals(id2sym(index), toSMT(from))),
              (if(intType == Int32Type)
                FixedSizeBitVectors.SLessThan(id2sym(index), toSMT(to))
              else
                Ints.LessThan(id2sym(index), toSMT(to)))),
            rSubstBody
          )
        )
      case BoundedExists(from, to, pred) =>
        val intType = from.getType
        val index = FreshIdentifier("i", intType)
        declareVariable(index)

        val Lambda(Seq(ValDef(el)), predBody) = pred
        val substBody = replaceFromIDs(Map(el -> index.toVariable), predBody)
        val rSubstBody = toSMT(substBody)

        SMTExists(
          SortedVar(id2sym(index), declareSort(intType)), Seq(),
          Core.And(
            (if(intType == Int32Type)
              FixedSizeBitVectors.SGreaterEquals(id2sym(index), toSMT(from))
            else
              Ints.GreaterEquals(id2sym(index), toSMT(from))),
            (if(intType == Int32Type)
              FixedSizeBitVectors.SLessThan(id2sym(index), toSMT(to))
            else
              Ints.LessThan(id2sym(index), toSMT(to))),
            rSubstBody
          )
        )

      case o =>
        unsupported(o, "")
    }
  }

  /* Translate an SMTLIB term back to a Leon Expr */
  protected def fromSMT(t: Term, otpe: Option[TypeTree] = None)(implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): Expr = {

    object EQ {
      def unapply(t: Term): Option[(Term, Term)] = t match {
        case Core.Equals(e1, e2) => Some((e1, e2))
        case FunctionApplication(f, Seq(e1, e2)) if f.toString == "=" => Some((e1, e2))
        case _ => None
      }
    }

    object AND {
      def unapply(t: Term): Option[Seq[Term]] = t match {
        case Core.And(e1, e2) => Some(Seq(e1, e2))
        case FunctionApplication(SimpleSymbol(SSymbol("and")), args) => Some(args)
        case _ => None
      }
      def apply(ts: Seq[Term]): Term = ts match {
        case Seq() => throw new IllegalArgumentException
        case Seq(t) => t
        case _ => FunctionApplication(SimpleSymbol(SSymbol("and")), ts)
      }
    }

    object Num {
      def unapply(t: Term): Option[BigInt] = t match {
        case SNumeral(n) => Some(n)
        case FunctionApplication(f, Seq(SNumeral(n))) if f.toString == "-" => Some(-n)
        case _ => None
      }
    }

    def extractLambda(n: BigInt, ft: FunctionType): Expr = {
      val FunctionType(from, to) = ft
      lambdas.getB(ft) match {
        case None => simplestValue(ft)
        case Some(dynLambda) => letDefs.get(dynLambda) match {
          case None => simplestValue(ft)
          case Some(DefineFun(SMTFunDef(a, SortedVar(dispatcher, dkind) +: args, rkind, body))) =>
            val lambdaArgs = from.map(tpe => FreshIdentifier("x", tpe, true))
            val argsMap: Map[Term, Identifier] = (args.map(sv => symbolToQualifiedId(sv.name)) zip lambdaArgs).toMap

            val d = symbolToQualifiedId(dispatcher)
            def dispatch(t: Term): Term = t match {
              case Core.ITE(EQ(di, Num(ni)), thenn, elze) if di == d =>
                if (ni == n) thenn else dispatch(elze)
              case Core.ITE(AND(EQ(di, Num(ni)) +: rest), thenn, elze) if di == d =>
                if (ni == n) Core.ITE(AND(rest), thenn, dispatch(elze)) else dispatch(elze)
              case _ => t
            }

            def extract(t: Term): Expr = {
              def recCond(term: Term): Seq[Expr] = term match {
                case AND(es) =>
                  es.foldLeft(Seq.empty[Expr]) {
                    case (seq, e) => seq ++ recCond(e)
                  }
                case EQ(e1, e2) =>
                  argsMap.get(e1).map(l => l -> e2) orElse argsMap.get(e2).map(l => l -> e1) match {
                    case Some((lambdaArg, term)) => Seq(Equals(lambdaArg.toVariable, fromSMT(term, lambdaArg.getType)))
                    case _ => Seq.empty
                  }
                case arg =>
                  argsMap.get(arg) match {
                    case Some(lambdaArg) => Seq(lambdaArg.toVariable)
                    case _ => Seq.empty
                  }
              }

              def recCases(term: Term): Expr = term match {
                case Core.ITE(cond, thenn, elze) =>
                  IfExpr(andJoin(recCond(cond)), recCases(thenn), recCases(elze))
                case AND(es) if to == BooleanType =>
                  andJoin(recCond(term))
                case EQ(e1, e2) if to == BooleanType =>
                  andJoin(recCond(term))
                case _ =>
                 fromSMT(term, to)
              }

              val body = recCases(t)
              Lambda(lambdaArgs.map(ValDef(_)), body)
            }

            extract(dispatch(body))
        }
      }
    }

    // Use as much information as there is, if there is an expected type, great, but it might not always be there
    (t, otpe) match {
      case (_, Some(UnitType)) =>
        UnitLiteral()

      case (FixedSizeBitVectors.BitVectorConstant(n, b), Some(CharType)) if b == BigInt(32) =>
        CharLiteral(n.toInt.toChar)

      case (FixedSizeBitVectors.BitVectorConstant(n, b), Some(Int8Type)) if b == BigInt(8) =>
        ByteLiteral(b.toByte)

      case (FixedSizeBitVectors.BitVectorConstant(n, b), Some(Int32Type)) if b == BigInt(32) =>
        IntLiteral(n.toInt)

      case (SHexadecimal(h), Some(CharType)) =>
        CharLiteral(h.toInt.toChar)

      case (SHexadecimal(hexa), Some(Int8Type)) =>
        ByteLiteral(hexa.toInt.toByte)

      case (SHexadecimal(hexa), Some(Int32Type)) =>
        IntLiteral(hexa.toInt)

      case (SDecimal(d), Some(RealType)) =>
        // converting bigdecimal to a fraction
        if (d == BigDecimal(0))
          FractionalLiteral(0, 1)
        else {
          d.toBigIntExact() match {
            case Some(num) =>
              FractionalLiteral(num, 1)
            case _ =>
              val scale = d.scale
              val num = BigInt(d.bigDecimal.scaleByPowerOfTen(scale).toBigInteger())
              val denom = BigInt(new java.math.BigDecimal(1).scaleByPowerOfTen(scale).toBigInteger())
              FractionalLiteral(num, denom)
          }
        }

      case (Num(n), Some(ft: FunctionType)) =>
        extractLambda(n, ft)

      case (SNumeral(n), Some(RealType)) =>
        FractionalLiteral(n, 1)

      case (FunctionApplication(SimpleSymbol(SSymbol("ite")), Seq(cond, thenn, elze)), t) =>
        IfExpr(
          fromSMT(cond, Some(BooleanType)),
          fromSMT(thenn, t),
          fromSMT(elze, t))

      // Best-effort case
      case (SNumeral(n), _) =>
        InfiniteIntegerLiteral(n)

      // EK: Since we have no type information, we cannot do type-directed
      // extraction of defs, instead, we expand them in smt-world
      case (SMTLet(binding, bindings, body), tpe) =>
        val defsMap: Map[SSymbol, Term] = (binding +: bindings).map {
          case VarBinding(s, value) => (s, value)
        }.toMap

        fromSMT(body, tpe)(lets ++ defsMap, letDefs)

      case (SimpleSymbol(s), _) if constructors.containsB(s) =>
        constructors.toA(s) match {
          case cct: CaseClassType =>
            CaseClass(cct, Nil)
          case t =>
            unsupported(t, "woot? for a single constructor for non-case-object")
        }

      case (FunctionApplication(SimpleSymbol(s), List(e)), _) if testers.containsB(s) =>
        testers.toA(s) match {
          case cct: CaseClassType =>
            IsInstanceOf(fromSMT(e, cct), cct)
        }

      case (FunctionApplication(SimpleSymbol(s), List(e)), _) if selectors.containsB(s) =>
        selectors.toA(s) match {
          case (cct: CaseClassType, i) =>
            CaseClassSelector(cct, fromSMT(e, cct), cct.fields(i).id)
        }

      case (FunctionApplication(SimpleSymbol(s), args), _) if constructors.containsB(s) =>
        constructors.toA(s) match {
          case cct: CaseClassType =>
            val rargs = args.zip(cct.fields.map(_.getType)).map(fromSMT)
            CaseClass(cct, rargs)

          case tt: TupleType =>
            val rargs = args.zip(tt.bases).map(fromSMT)
            tupleWrap(rargs)

          case at @ ArrayType(baseType) =>
            val IntLiteral(size) = fromSMT(args(0), Int32Type)
            val RawArrayValue(_, elems, default) = fromSMT(args(1), RawArrayType(Int32Type, baseType))

            if (size < 0) {
              unsupported(at, "Cannot build an array of negative length: " + size)
            } else if (size > 10) {
              val definedElements = elems.collect {
                case (IntLiteral(i), value) => (i, value)
              }
              finiteArray(definedElements, Some(default, IntLiteral(size)), baseType)

            } else {
              val entries = for (i <- 0 to size - 1) yield elems.getOrElse(IntLiteral(i), default)

              finiteArray(entries, None, baseType)
            }

          case tp @ TypeParameter(id) =>
            val InfiniteIntegerLiteral(n) = fromSMT(args(0), IntegerType)
            GenericValue(tp, n.toInt)

          case t =>
            unsupported(t, "Woot? structural type that is non-structural")
        }

      case (FunctionApplication(SimpleSymbol(s @ SSymbol(app)), args), _) =>
        (app, args) match {
          case (">=", List(a, b)) =>
            GreaterEquals(fromSMT(a, IntegerType), fromSMT(b, IntegerType))

          case ("<=", List(a, b)) =>
            LessEquals(fromSMT(a, IntegerType), fromSMT(b, IntegerType))

          case (">", List(a, b)) =>
            GreaterThan(fromSMT(a, IntegerType), fromSMT(b, IntegerType))

          case (">", List(a, b)) =>
            LessThan(fromSMT(a, IntegerType), fromSMT(b, IntegerType))

          case ("+", args) =>
            args.map(fromSMT(_, otpe)).reduceLeft(plus _)

          case ("-", List(a)) if otpe == Some(RealType) =>
            val aexpr = fromSMT(a, otpe)
            aexpr match {
              case FractionalLiteral(na, da) =>
                FractionalLiteral(-na, da)
              case _ =>
                UMinus(aexpr)
            }

          case ("-", List(a)) =>
            val aexpr = fromSMT(a, otpe)
            aexpr match {
              case InfiniteIntegerLiteral(v) =>
                InfiniteIntegerLiteral(-v)
              case _ =>
                UMinus(aexpr)
            }

          case ("-", List(a, b)) =>
            Minus(fromSMT(a, otpe), fromSMT(b, otpe))

          case ("*", args) =>
            args.map(fromSMT(_, otpe)).reduceLeft(times _)

          case ("/", List(a, b)) if otpe == Some(RealType) =>
            val aexpr = fromSMT(a, otpe)
            val bexpr = fromSMT(b, otpe)
            (aexpr, bexpr) match {
              case (FractionalLiteral(na, da), FractionalLiteral(nb, db)) if da == 1 && db == 1 =>
                FractionalLiteral(na, nb)
              case _ =>
                Division(aexpr, bexpr)
            }

          case ("/", List(a, b)) =>
            Division(fromSMT(a, otpe), fromSMT(b, otpe))

          case ("div", List(a, b)) =>
            Division(fromSMT(a, otpe), fromSMT(b, otpe))

          case ("not", List(a)) =>
            Not(fromSMT(a, BooleanType))

          case ("or", args) =>
            orJoin(args.map(fromSMT(_, BooleanType)))

          case ("and", args) =>
            andJoin(args.map(fromSMT(_, BooleanType)))

          case ("=", List(a, b)) =>
            val ra = fromSMT(a, None)
            Equals(ra, fromSMT(b, ra.getType))

          case _ =>
            context.reporter.fatalError("Function " + app + " not handled in fromSMT: " + s)
        }

      case (Core.True(), Some(BooleanType))  => BooleanLiteral(true)
      case (Core.False(), Some(BooleanType)) => BooleanLiteral(false)

      case (SimpleSymbol(s), otpe) if lets contains s =>
        fromSMT(lets(s), otpe)

      case (SimpleSymbol(s), otpe) =>
        variables.getA(s).map(_.toVariable).getOrElse {
          throw new Exception()
        }

      case _ =>
        context.reporter.fatalError(s"Unhandled case in fromSMT: $t : ${otpe.map(_.asString(context)).getOrElse("?")} (${t.getClass})")

    }
  }

  final protected def fromSMT(pair: (Term, TypeTree))(implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): Expr = {
    fromSMT(pair._1, Some(pair._2))
  }

  final protected def fromSMT(s: Term, tpe: TypeTree)(implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): Expr = {
    fromSMT(s, Some(tpe))
  }
}

// Unique numbers
private[smtlib] object DebugFileNumbers extends UniqueCounter[String]
