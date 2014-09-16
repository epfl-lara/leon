package leon
package solvers
package smtlib

import utils.Interruptible
import purescala._
import Common._
import Trees.{Assert => _, _}
import Extractors._
import TreeOps._
import TypeTrees._
import Definitions._
import utils.Bijection

import _root_.smtlib.common._
import _root_.smtlib.printer.{PrettyPrinter => SMTPrinter}
import _root_.smtlib.parser.Commands.{Constructor => SMTConstructor, _}
import _root_.smtlib.parser.Terms.{Identifier => SMTIdentifier, Let => SMTLet, _}
import _root_.smtlib.parser.CommandsResponses.{Error => ErrorResponse, _}
import _root_.smtlib.theories._
import _root_.smtlib.{Interpreter => SMTInterpreter}

trait SMTLIBTarget {
  this: SMTLIBSolver =>

  val reporter = context.reporter

  def targetName: String
  def getNewInterpreter(): SMTInterpreter

  val interpreter = getNewInterpreter()

  val out = new java.io.FileWriter(s"vcs-$targetName.smt2", true)
  reporter.ifDebug { debug =>
    out.write("; -----------------------------------------------------\n")
  }

  def id2sym(id: Identifier): SSymbol = SSymbol(id.name+"!"+id.globalId)

  // metadata for CC, and variables
  val constructors = new Bijection[TypeTree, SSymbol]()
  val selectors    = new Bijection[(TypeTree, Int), SSymbol]()
  val testers      = new Bijection[TypeTree, SSymbol]()
  val variables    = new Bijection[Identifier, SSymbol]()
  val sorts        = new Bijection[TypeTree, Sort]()
  val functions    = new Bijection[TypedFunDef, SSymbol]()

  def normalizeType(t: TypeTree): TypeTree = t match {
    case ct: ClassType if ct.parent.isDefined => ct.parent.get
    case tt: TupleType => TupleType(tt.bases.map(normalizeType))
    case _ =>   t
  }

  // Corresponds to a smt map, not a leon/scala array
  // Should NEVER escape past SMT-world
  case class RawArrayType(from: TypeTree, to: TypeTree) extends TypeTree

  // Corresponds to a raw array value, which is coerced to a Leon expr depending on target type (set/array)
  // Should NEVER escape past SMT-world
  case class RawArrayValue(keyTpe: TypeTree, elems: Map[Expr, Expr], default: Expr) extends Expr

  def unsupported(str: Any) = reporter.fatalError(s"Unsupported in smt-$targetName: $str")

  def declareSort(t: TypeTree): Sort = {
    val tpe = normalizeType(t)
    sorts.cachedB(tpe) {
      tpe match {
        case BooleanType => Core.BoolSort()
        case Int32Type => Ints.IntSort()

        case RawArrayType(from, to) =>
          Sort(SMTIdentifier(SSymbol("Array")), Seq(declareSort(from), declareSort(to)))

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

  def freshSym(id: Identifier): SSymbol = freshSym(id.name)
  def freshSym(name: String): SSymbol = id2sym(FreshIdentifier(name))

  def declareStructuralSort(t: TypeTree): Sort = {

    def getHierarchy(ct: ClassType): (ClassType, Seq[CaseClassType]) = ct match {
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

    case class DataType(sym: SSymbol, cases: Seq[Constructor])
    case class Constructor(sym: SSymbol, tpe: TypeTree, fields: Seq[(SSymbol, TypeTree)])

    var datatypes = Map[TypeTree, DataType]()


    def findDependencies(t: TypeTree): Unit = t match {
      case ct: ClassType =>
        val (root, sub) = getHierarchy(ct)

        if (!(datatypes contains root) && !(sorts containsA root)) {
          val sym = freshSym(ct.id)

          val conss = sub.map { case cct =>
            Constructor(freshSym(cct.id), cct, cct.fields.map(vd => (freshSym(vd.id), vd.tpe)))
          }

          datatypes += root -> DataType(sym, conss)

          // look for dependencies
          for (ct <- root +: sub; f <- ct.fields) findDependencies(f.tpe)
        }
      case tt @ TupleType(bases) =>
        if (!(datatypes contains t) && !(sorts containsA t)) {
          val sym = freshSym("tuple"+bases.size)

          val c = Constructor(freshSym(sym.name), tt, bases.zipWithIndex.map {
            case (tpe, i) => (freshSym("_"+(i+1)), tpe)
          })

          datatypes += tt -> DataType(sym, Seq(c))

          bases.foreach(findDependencies)
        }

      case UnitType =>
        if (!(datatypes contains t) && !(sorts containsA t)) {

          val sym = freshSym("Unit")

          datatypes += t -> DataType(sym, Seq(Constructor(freshSym(sym.name), t, Nil)))
        }

      case at @ ArrayType(base) =>
        if (!(datatypes contains t) && !(sorts containsA t)) {
          val sym = freshSym("array")

          val c = Constructor(freshSym(sym.name), at, List(
            (freshSym("size"), Int32Type),
            (freshSym("content"), RawArrayType(Int32Type, base))
          ))

          datatypes += at -> DataType(sym, Seq(c))

          findDependencies(base)
        }

      case _ =>
    }

    // Populates the dependencies of the structural type to define.
    findDependencies(t)

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

    sorts.toB(t)
  }

  def declareVariable(id: Identifier): SSymbol = {
    variables.cachedB(id) {
      val s = id2sym(id)
      val cmd = DeclareFun(s, List(), declareSort(id.getType))
      sendCommand(cmd)
      s
    }
  }

  def declareFunction(tfd: TypedFunDef): SSymbol = {
    functions.cachedB(tfd) {
      val id = if (tfd.tps.isEmpty) {
        tfd.id
      } else {
        FreshIdentifier(tfd.id.name)
      }
      val s = id2sym(id)
      sendCommand(DeclareFun(s, tfd.params.map(p => declareSort(p.tpe)), declareSort(tfd.returnType)))
      s
    }
  }

  def toSMT(e: Expr)(implicit bindings: Map[Identifier, Term]): Term = {
    e match {
      case Variable(id) =>
        declareSort(e.getType)
        bindings.getOrElse(id, variables.toB(id))

      case UnitLiteral() =>
        declareSort(UnitType)

        declareVariable(FreshIdentifier("Unit").setType(UnitType))

      case IntLiteral(i) => if (i > 0) Ints.NumeralLit(i) else Ints.Neg(Ints.NumeralLit(-i))
      case BooleanLiteral(v) => Core.BoolConst(v)
      case StringLiteral(s) => SString(s)
      case Let(b,d,e) =>
        val id      = id2sym(b)
        val value   = toSMT(d)
        val newBody = toSMT(e)(bindings + (b -> id))

        SMTLet(
          VarBinding(id, value),
          Seq(),
          newBody
        )

      case er @ Error(_) =>
        val s = declareVariable(FreshIdentifier("error_value").setType(er.getType))
        s

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


      case e @ UnaryOperator(u, _) =>
        e match {
          case (_: Not) => Core.Not(toSMT(u))
          case (_: UMinus) => Ints.Neg(toSMT(u))
          case _ => reporter.fatalError("Unhandled unary "+e)
        }

      case e @ BinaryOperator(a, b, _) =>
        e match {
          case (_: Equals) => Core.Equals(toSMT(a), toSMT(b))
          case (_: Implies) => Core.Implies(toSMT(a), toSMT(b))
          case (_: Iff) => Core.Equals(toSMT(a), toSMT(b))
          case (_: Plus) => Ints.Add(toSMT(a), toSMT(b))
          case (_: Minus) => Ints.Sub(toSMT(a), toSMT(b))
          case (_: Times) => Ints.Mul(toSMT(a), toSMT(b))
          case (_: Division) => Ints.Div(toSMT(a), toSMT(b))
          case (_: Modulo) => Ints.Mod(toSMT(a), toSMT(b))
          case (_: LessThan) => Ints.LessThan(toSMT(a), toSMT(b))
          case (_: LessEquals) => Ints.LessEquals(toSMT(a), toSMT(b))
          case (_: GreaterThan) => Ints.GreaterThan(toSMT(a), toSMT(b))
          case (_: GreaterEquals) => Ints.GreaterEquals(toSMT(a), toSMT(b))
          case _ => reporter.fatalError("Unhandled binary "+e)
        }

      case e @ NAryOperator(sub, _) =>
        e match {
          case (_: And) => Core.And(sub.map(toSMT): _*)
          case (_: Or) => Core.Or(sub.map(toSMT): _*)
          case (_: IfExpr) => Core.ITE(toSMT(sub(0)), toSMT(sub(1)), toSMT(sub(2))) 
          case (f: FunctionInvocation) => 
            FunctionApplication(
              declareFunction(f.tfd),
              sub.map(toSMT)
            )
          case _ => reporter.fatalError("Unhandled nary "+e)
        }


      case o => unsupported("Tree: " + o)
    }
  }

  def fromSMT(pair: (Term, TypeTree))(implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): Expr = {
    fromSMT(pair._1, pair._2)
  }

  def fromSMT(s: Term, tpe: TypeTree)(implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): Expr = (s, tpe) match {
    case (_, UnitType) =>
      UnitLiteral()

    case (SNumeral(n), Int32Type) =>
      IntLiteral(n.toInt)

    case (Core.True(), BooleanType)  => BooleanLiteral(true)
    case (Core.False(), BooleanType)  => BooleanLiteral(false)

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
          val rargs = args.zip(cct.fields.map(_.tpe)).map(fromSMT)
          CaseClass(cct, rargs)
        case tt: TupleType =>
          val rargs = args.zip(tt.bases).map(fromSMT)
          Tuple(rargs)

        case at: ArrayType =>
          val IntLiteral(size)                 = fromSMT(args(0), Int32Type)
          val RawArrayValue(_, elems, default) = fromSMT(args(1), RawArrayType(Int32Type, at.base))

          val entries = for (i <- 0 to size-1) yield elems.getOrElse(IntLiteral(i), default)

          FiniteArray(entries).setType(at)

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
            case List(a) => UMinus(fromSMT(a, Int32Type))
            case List(a, b) => Minus(fromSMT(a, Int32Type), fromSMT(b, Int32Type))
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

  def sendCommand(cmd: Command): CommandResponse = {
    reporter.ifDebug { debug =>
      SMTPrinter.printCommand(cmd, out)
      out.write("\n")
      out.flush
    }

    interpreter.eval(cmd) match {
      case ErrorResponse(msg) =>
        reporter.fatalError("Unnexpected error from smt-"+targetName+" solver: "+msg)
      case res => res
    }
  }

  override def assertCnstr(expr: Expr): Unit = {
    variablesOf(expr).foreach(declareVariable)
    val term = toSMT(expr)(Map())
    sendCommand(Assert(term))
  }

  override def check: Option[Boolean] = sendCommand(CheckSat()) match {
    case CheckSatResponse(SatStatus)     => Some(true)
    case CheckSatResponse(UnsatStatus)   => Some(false)
    case CheckSatResponse(UnknownStatus) => None
    case _                               => None
  }

  override def getModel: Map[Identifier, Expr] = {
    val syms = variables.bSet.toList
    val cmd: Command = 
      GetValue(syms.head, 
               syms.tail.map(s => QualifiedIdentifier(SMTIdentifier(s)))
              )


    val GetValueResponse(valuationPairs) = sendCommand(cmd)

    valuationPairs.collect {
      case (SimpleSymbol(sym), value) if variables.containsB(sym) =>
        val id = variables.toA(sym)

        (id, fromSMT(value, id.getType)(Map(), Map()))
    }.toMap
  }

  override def push(): Unit = {
    sendCommand(Push(1))
  }
  override def pop(lvl: Int = 1): Unit = {
    sendCommand(Pop(1))
  }

  protected object SimpleSymbol {

    def unapply(term: Term): Option[SSymbol] = term match {
      case QualifiedIdentifier(SMTIdentifier(sym, Seq()), None) => Some(sym)
      case _ => None
    }

  }

  import scala.language.implicitConversions
  implicit def symbolToQualifiedId(s: SSymbol): QualifiedIdentifier = {
    QualifiedIdentifier(SMTIdentifier(s))
  }

}
