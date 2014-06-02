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

import _root_.smtlib.{PrettyPrinter => SMTPrinter, Interpreter => SMTInterpreter}
import _root_.smtlib.Commands.{Identifier => _, _}
import _root_.smtlib.CommandResponses.{Error => ErrorResponse, _}
import _root_.smtlib.sexpr.SExprs._
import _root_.smtlib.interpreters._

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
  val sorts        = new Bijection[TypeTree, SExpr]()
  val functions    = new Bijection[TypedFunDef, SSymbol]()

  def normalizeType(t: TypeTree): TypeTree = t match {
    case ct: ClassType if ct.parent.isDefined => ct.parent.get
    case tt: TupleType => TupleType(tt.bases.map(normalizeType))
    case _ =>   t
  }

  def unsupported(str: Any) = reporter.fatalError(s"Unsupported in $targetName: $str")

  def declareSort(t: TypeTree): SExpr = {
    val tpe = normalizeType(t)
    sorts.cachedB(tpe) {
      tpe match {
        case BooleanType => SSymbol("Bool")
        case Int32Type => SSymbol("Int")
        case UnitType =>
          val s = SSymbol("Unit")
          val cmd = NonStandardCommand(SList(SSymbol("declare-sort"), s))
          sendCommand(cmd)
          s
        case TypeParameter(id) =>
          val s = id2sym(id)
          val cmd = NonStandardCommand(SList(SSymbol("declare-sort"), s))
          sendCommand(cmd)
          s
        case _: ClassType | _: TupleType =>
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
        if (!(datatypes contains tt) && !(sorts containsA tt)) {
          val sym = freshSym("tuple"+bases.size)

          val c = Constructor(freshSym(sym.s), tt, bases.zipWithIndex.map {
            case (tpe, i) => (freshSym("_"+(i+1)), tpe)
          })

          datatypes += tt -> DataType(sym, Seq(c))

          bases.foreach(findDependencies)
        }

      case st @ SetType(base) =>


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

      case IntLiteral(v) => SInt(v)
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
        SList(selectors.toB((cct, s.selectorIndex)), toSMT(e))

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
        SList(selectors.toB((tpe, i-1)), toSMT(t))

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

  def extractSpecialSymbols(s: SSymbol): Option[Expr] = {
    None
  }

  def fromSMT(s: SExpr)(implicit bindings: Map[SSymbol, Expr]): Expr = s match {
    case SInt(n)          => IntLiteral(n.toInt)
    case SSymbol("true")  => BooleanLiteral(true)
    case SSymbol("false") => BooleanLiteral(false)
    case s: SSymbol if constructors.containsB(s) =>
      constructors.toA(s) match {
        case cct: CaseClassType =>
          CaseClass(cct, Nil)
        case t =>
          unsupported("woot? for a single constructor for non-case-object: "+t)
      }

    case s: SSymbol =>
      (bindings.get(s) orElse variables.getA(s).map(_.toVariable)
                       orElse extractSpecialSymbols(s)).getOrElse {
        unsupported("Unknown symbol: "+s)
      }

    case SList((s: SSymbol) :: args) if(constructors.containsB(s)) => 
      val rargs = args.map(fromSMT)
      constructors.toA(s) match {
        case cct: CaseClassType =>
          CaseClass(cct, rargs)
        case tt: TupleType =>
          Tuple(rargs)
        case t =>
          unsupported("Woot? structural type that is non-structural: "+t)
      }

    case SList(List(SSymbol("let"), SList(defs), body)) =>
      val leonDefs: Seq[(SSymbol, Identifier, Expr)] = defs.map {
        case SList(List(s : SSymbol, value)) =>
          (s, FreshIdentifier(s.s), fromSMT(value))
      }

      val newBindings = bindings ++ leonDefs.map(d => d._1 -> d._3)
      val newBody = fromSMT(body)(newBindings)

      LetTuple(leonDefs.map(_._2), Tuple(leonDefs.map(_._3)), newBody)

    case SList(SSymbol(app) :: args) => {
      val recArgs = args.map(fromSMT)

      app match {
        case "-" =>
          recArgs match {
            case List(a) => UMinus(a)
            case List(a, b) => Minus(a, b)
          }

        case _ =>
          unsupported(s)
      }
    }
    case _ =>
      unsupported(s)
  }

  def sendCommand(cmd: Command): CommandResponse = {
    reporter.ifDebug { debug =>
      SMTPrinter(cmd, out)
      out.write("\n")
      out.flush
    }

    val response = interpreter.eval(cmd)
    assert(!response.isInstanceOf[Error])
    response
  }

  override def assertCnstr(expr: Expr): Unit = {
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
        (variables.toA(sym), fromSMT(value)(Map()))
    }.toMap
  }

  override def push(): Unit = {
    sendCommand(Push(1))
  }
  override def pop(lvl: Int = 1): Unit = {
    sendCommand(Pop(1))
  }
}
