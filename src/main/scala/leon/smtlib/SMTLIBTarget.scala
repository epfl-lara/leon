package leon
package smtlib
import purescala._
import purescala.Trees._
import purescala.Common._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._
import utils.Bijection


import _root_.smtlib.{PrettyPrinter => SMTPrinter, Interpreter => SMTInterpreter}
import _root_.smtlib.Commands.{Identifier => _, _}
import _root_.smtlib.CommandResponses.{Error => ErrorResponse, _}
import _root_.smtlib.sexpr.SExprs._
import _root_.smtlib.interpreters._
import scala.math.BigInt.int2bigInt

abstract class SMTLIBTarget(context: LeonContext) {

  val reporter = context.reporter

  def targetName: String
  def getNewInterpreter(): SMTInterpreter

  val interpreter = getNewInterpreter()

  val out = new java.io.FileWriter(s"vcs-$targetName.smt2", true)
  /*reporter.ifDebug { debug =>
    out.write("; -----------------------------------------------------\n")
  }*/

  def id2sym(id: Identifier): SSymbol = SSymbol(id.name+"!"+id.id)

  // metadata for CC, and variables
  val constructors = new Bijection[TypeTree, SSymbol]()
  val selectors    = new Bijection[(TypeTree, Int), SSymbol]()
  val testers      = new Bijection[TypeTree, SSymbol]()
  val variables    = new Bijection[Identifier, SSymbol]()
  val sorts        = new Bijection[TypeTree, SExpr]()
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

  def declareSort(t: TypeTree): SExpr = {
    val tpe = normalizeType(t)
    sorts.cachedB(tpe) {
      tpe match {
        case BooleanType => SSymbol("Bool")
        case Int32Type => SSymbol("Int")

        case RawArrayType(from, to) =>
          SList(SSymbol("Array"), declareSort(from), declareSort(to))

        case TypeParameter(id) =>
          val s = id2sym(id)
          val cmd = NonStandardCommand(SList(SSymbol("declare-sort"), s))
          sendCommand(cmd)
          s
        case _: ClassType | _: TupleType | _: ArrayType | UnitType =>
          declareStructuralSort(tpe)
        case _ =>
          unsupported("Sort "+t)
      }
    }
  }

  def freshSym(id: Identifier): SSymbol = freshSym(id.name)
  def freshSym(name: String): SSymbol = id2sym(FreshIdentifier(name))

  def declareStructuralSort(t: TypeTree): SExpr = {

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

          val c = Constructor(freshSym(sym.s), tt, bases.zipWithIndex.map {
            case (tpe, i) => (freshSym("_"+(i+1)), tpe)
          })

          datatypes += tt -> DataType(sym, Seq(c))

          bases.foreach(findDependencies)
        }

      case UnitType =>
        if (!(datatypes contains t) && !(sorts containsA t)) {

          val sym = freshSym("Unit")

          datatypes += t -> DataType(sym, Seq(Constructor(freshSym(sym.s), t, Nil)))
        }

      case at @ ArrayType(base) =>
        if (!(datatypes contains t) && !(sorts containsA t)) {
          val sym = freshSym("array")

          val c = Constructor(freshSym(sym.s), at, List(
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
      sorts += tpe -> sym
    }

    def toDecl(c: Constructor): SExpr = {
      val s = c.sym

      testers += c.tpe -> SSymbol("is-"+s.s)
      constructors += c.tpe -> s

      SList(s :: c.fields.zipWithIndex.map {
        case ((cs, t), i) =>
          selectors += (c.tpe, i) -> cs
          SList(cs, declareSort(t))
      }.toList)
    }

    val adts = for ((tpe, DataType(sym, cases)) <- datatypes.toList) yield {
      SList(sym :: cases.map(toDecl).toList)
    }


    val cmd = NonStandardCommand(SList(SSymbol("declare-datatypes"), SList(), SList(adts)))
    sendCommand(cmd)

    sorts.toB(t)
  }

  def declareVariable(id: Identifier): SSymbol = {
    variables.cachedB(id) {
      val s = id2sym(id)
      val cmd = NonStandardCommand(SList(SSymbol("declare-const"), s, declareSort(id.getType)))
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
      sendCommand(DeclareFun(s.s, tfd.params.map(p => declareSort(p.tpe)), declareSort(tfd.returnType)))
      s
    }
  }

  def toSMT(e: Expr)(implicit bindings: Map[Identifier, SExpr]): SExpr = {
    e match {
      case Variable(id) =>
        declareSort(e.getType)
        bindings.getOrElse(id, variables.toB(id))

      case UnitLiteral() =>
        declareSort(UnitType)
        declareVariable(FreshIdentifier("Unit").setType(UnitType))

      case IntLiteral(i) => if (i > 0) SInt(i) else SList(SSymbol("-"), SInt(-i))
      case BooleanLiteral(v) => SSymbol(if (v) "true" else "false")
      case StringLiteral(s) => SString(s)
      case Let(b,d,e) =>
        val id      = id2sym(b)
        val value   = toSMT(d)
        val newBody = toSMT(e)(bindings + (b -> id))

        SList(
          SSymbol("let"),
          SList(
            SList(id, value)
          ),
          newBody
        )

      case er @ Error(_) =>
        declareVariable(FreshIdentifier("error_value").setType(er.getType))

      case s @ CaseClassSelector(cct, e, id) =>
        declareSort(cct)
        SList(selectors.toB((cct, cct.fields.map(_.id).indexOf(s.selector.id))), toSMT(e))

      case CaseClassInstanceOf(cct, e) =>
        declareSort(cct)
        SList(testers.toB(cct), toSMT(e))

      case CaseClass(cct, es) =>
        declareSort(cct)
        if (es.isEmpty) {
          constructors.toB(cct)
        } else {
          SList(constructors.toB(cct) :: es.map(toSMT).toList)
        }

      case t @ Tuple(es) =>
        val tpe = normalizeType(t.getType)
        declareSort(tpe)
        SList(constructors.toB(tpe) :: es.map(toSMT).toList)

      case ts @ TupleSelect(t, i) =>
        val tpe = normalizeType(t.getType)
        declareSort(tpe)
        SList(selectors.toB((tpe, i-1)), toSMT(t))

      case al @ ArrayLength(a) =>
        val tpe = normalizeType(a.getType)
        SList(selectors.toB((tpe, 0)), toSMT(a))

      case as @ ArraySelect(a, i) =>
        val tpe = normalizeType(a.getType)
        SList(SSymbol("select"), SList(selectors.toB((tpe, 1)), toSMT(a)), toSMT(i))

      case as @ ArrayUpdated(a, i, e) =>
        val tpe = normalizeType(a.getType)

        val ssize    = SList(selectors.toB((tpe, 0)), toSMT(a))
        val scontent = SList(selectors.toB((tpe, 1)), toSMT(a))

        SList(constructors.toB(tpe), ssize, SList(SSymbol("store"), scontent, toSMT(i), toSMT(e)))


      case e @ UnaryOperator(u, _) =>
        val op = e match {
          case _: Not => SSymbol("not")
          case _: UMinus => SSymbol("-")
          case _ => reporter.fatalError("Unhandled unary "+e)
        }

        SList(op :: List(u).map(toSMT))

      case e @ BinaryOperator(a, b, _) =>
        val op = e match {
          case _: Equals => SSymbol("=")
          case _: Implies => SSymbol("=>")
          case _: Iff => SSymbol("=")
          case _: Plus => SSymbol("+")
          case _: Minus => SSymbol("-")
          case _: Times => SSymbol("*")
          case _: Division => SSymbol("div")
          case _: Modulo => SSymbol("mod")
          case _: LessThan => SSymbol("<")
          case _: LessEquals => SSymbol("<=")
          case _: GreaterThan => SSymbol(">")
          case _: GreaterEquals => SSymbol(">=")
          case _ => reporter.fatalError("Unhandled binary "+e)
        }

        SList(op :: List(a, b).map(toSMT))

      case e @ NAryOperator(sub, _) =>
        val op = e match {
          case _: And => SSymbol("and")
          case _: Or => SSymbol("or")
          case _: IfExpr => SSymbol("ite")
          case f: FunctionInvocation => declareFunction(f.tfd)
          case _ => reporter.fatalError("Unhandled nary "+e)
        }

        SList(op :: sub.map(toSMT).toList)


      case o => unsupported("Tree: " + o)
    }
  }

  def fromSMT(pair: (SExpr, TypeTree))(implicit letDefs: Map[SSymbol, SExpr]): Expr = {
    fromSMT(pair._1, pair._2)
  }

  def fromSMT(s: SExpr, tpe: TypeTree)(implicit letDefs: Map[SSymbol, SExpr]): Expr = (s, tpe) match {
    case (_, UnitType) =>
      UnitLiteral()

    case (SInt(n), Int32Type) =>
      IntLiteral(n.toInt)

    case (SSymbol(s), BooleanType)  =>
      BooleanLiteral(s == "true")

    case (s: SSymbol, _: ClassType) if constructors.containsB(s) =>
      constructors.toA(s) match {
        case cct: CaseClassType =>
          CaseClass(cct, Nil)
        case t =>
          unsupported("woot? for a single constructor for non-case-object: "+t)
      }

    case (s: SSymbol, tpe) if letDefs contains s =>
      fromSMT(letDefs(s), tpe)

    case (s: SSymbol, _) =>
      variables.getA(s).map(_.toVariable).getOrElse {
        unsupported("Unknown symbol: "+s)
      }

    case (SList((s: SSymbol) :: args), tpe) if constructors.containsB(s) =>
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
    case (SList(List(SSymbol("let"), SList(defs), body)), tpe) =>
      val defsMap: Map[SSymbol, SExpr] = defs.map {
        case SList(List(s : SSymbol, value)) =>
          (s, value)
      }.toMap

      fromSMT(body, tpe)(letDefs ++ defsMap)

    case (SList(SSymbol(app) :: args), tpe) => {
      app match {
        case "-" =>
          args match {
            case List(a) => UMinus(fromSMT(a, Int32Type))
            case List(a, b) => Minus(fromSMT(a, Int32Type), fromSMT(b, Int32Type))
          }

        case _ =>
          unsupported(s)
      }
    }
    case _ =>
      unsupported(s)
  }

  def sendCommand(cmd: Command): CommandResponse = {
    /*reporter.info{
      SMTPrinter(cmd, out)    
      out.write("\n")
      out.flush
    }*/

    interpreter.eval(cmd) match {
      case ErrorResponse(msg) =>
        reporter.fatalError("Unnexpected error from smt-"+targetName+" solver: "+msg)
      case res => res
    }
  }

  /*override def assertCnstr(expr: Expr): Unit = {
    variablesOf(expr).foreach(declareVariable)
    val sexpr = toSMT(expr)(Map())
    sendCommand(Assert(sexpr))
  }

  override def check: Option[Boolean] = sendCommand(CheckSat) match {
    case CheckSatResponse(SatStatus)     => Some(true)
    case CheckSatResponse(UnsatStatus)   => Some(false)
    case CheckSatResponse(UnknownStatus) => None
  }

  override def getModel: Map[Identifier, Expr] = {
    val syms = variables.bSet.toList
    val cmd: Command = GetValue(syms.head, syms.tail)

    val GetValueResponse(valuationPairs) = sendCommand(cmd)

    valuationPairs.collect {
      case (sym: SSymbol, value) if variables.containsB(sym) =>
        val id = variables.toA(sym)

        (id, fromSMT(value, id.getType)(Map()))
    }.toMap
  }

  override def push(): Unit = {
    sendCommand(Push(1))
  }
  override def pop(lvl: Int = 1): Unit = {
    sendCommand(Pop(1))
  }*/
}
