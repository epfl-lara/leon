package leon
package smtlib

import java.io._

import utils._
import purescala._
import purescala.Common._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._

import _root_.smtlib.sexpr.SExprs._
import _root_.smtlib.Commands.{GetValue, NonStandardCommand, Command}
import _root_.smtlib.CommandResponses.SExprResponse
import _root_.smtlib.CommandResponses._
import _root_.smtlib._

class ExprToSMTLIB(ctx: LeonContext){

  var commands = List[Command]()
  val target = new SMTLIBZ3Target(ctx) {
    def getNewInterpreter() = new Interpreter {
      override def eval(cmd: Command): CommandResponse = {
        commands :+= cmd
        Success
      }

      override def free(): Unit = {
        //nothing to be done here
      }
    }
  }
  
  def getCommands = commands
  
  def toSExprAndDefinitions(expr: Expr) : (List[Command],SExpr) = {
    variablesOf(expr).foreach(target.declareVariable)
    val sexpr = target.toSMT(expr)(Map())
    (commands, sexpr)
  }
}

abstract class SMTLIBZ3Target(context: LeonContext) extends SMTLIBTarget(context) {  

  def targetName = "z3"  

  val extSym = SSymbol("_")

  var setSort: Option[SSymbol] = None
  var mapSort: Option[SSymbol] = None
  var optionSort: Option[SSymbol] = None

  override def declareSort(t: TypeTree): SExpr = {
    val tpe = normalizeType(t)
    sorts.cachedB(tpe) {
      tpe match {
        case MapType(from, to) =>
          declareMapSort(from, to)
        case SetType(base) =>
          declareSetSort(base)
        case _ =>
          super.declareSort(t)
      }
    }
  }

  def declareSetSort(of: TypeTree) = {
    setSort match {
      case None =>
        val s = SSymbol("Set")
        val t = SSymbol("T")
        setSort = Some(s)

        val cmd = NonStandardCommand(SList(SSymbol("define-sort"), s, SList(t), SList(SSymbol("Array"), t, SSymbol("Bool"))))
        sendCommand(cmd)
      case _ =>
    }

    SList(setSort.get, declareSort(of))
  }

  def declareOptionSort(of: TypeTree) = {
    optionSort match {
      case None =>
        val t      = SSymbol("T")

        val s      = SSymbol("Option")
        val some   = SSymbol("Some")
        val some_v = SSymbol("Some_v")
        val none   = SSymbol("None")

        val caseSome = SList(some, SList(some_v, t))
        val caseNone = none

        val cmd = NonStandardCommand(SList(SSymbol("declare-datatypes"), SList(t), SList(SList(s, caseSome, caseNone))))
        sendCommand(cmd)

        optionSort = Some(s)
      case _ =>
    }

    SList(optionSort.get, declareSort(of))
  }

  def declareMapSort(from: TypeTree, to: TypeTree) = {
    mapSort match {
      case None =>
        val m = SSymbol("Map")
        val a = SSymbol("A")
        val b = SSymbol("B")
        mapSort = Some(m)
        declareOptionSort(to)

        val cmd = NonStandardCommand(SList(SSymbol("define-sort"), m, SList(a, b), SList(SSymbol("Array"), a, SList(optionSort.get, b))))
        sendCommand(cmd)
      case _ =>
    }

    SList(mapSort.get, declareSort(from), declareSort(to))
  }

  override def toSMT(e: Expr)(implicit bindings: Map[Identifier, SExpr]) = e match {
      case a @ FiniteArray(elems) =>
        val tpe @ ArrayType(base) = normalizeType(a.getType)
        declareSort(tpe)

        var ar = SList(SList(SSymbol("as"), SSymbol("const"), declareSort(RawArrayType(Int32Type, base))), 
            toSMT(simplestValue(base)))

        for ((e, i) <- elems.zipWithIndex) {
          ar = SList(SSymbol("store"), ar, toSMT(IntLiteral(i)), toSMT(e))
        }

        SList(constructors.toB(tpe), toSMT(IntLiteral(elems.size)), ar)

      /**
       * ===== Map operations =====
       */
      case MapGet(m, k) =>
        declareSort(m.getType)
        SList(SSymbol("Some_v"), SList(SSymbol("select"), toSMT(m), toSMT(k)))

      case MapIsDefinedAt(m, k) =>
        declareSort(m.getType)
        SList(SSymbol("is-Some"), SList(SSymbol("select"), toSMT(m), toSMT(k)))

      case m @ FiniteMap(elems) =>
        val ms = declareSort(m.getType)

        var res = SList(SList(SSymbol("as"), SSymbol("const"), ms), SSymbol("None"))
        for ((k, v) <- elems) {
          res = SList(SSymbol("store"), res, toSMT(k), SList(SSymbol("Some"), toSMT(v)))
        }

        res

      /**
       * ===== Set operations =====
       */
      case fs @ FiniteSet(elems) =>
        val ss = declareSort(fs.getType)
        var res = SList(SList(SSymbol("as"), SSymbol("const"), ss), toSMT(BooleanLiteral(false)))

        for (e <- elems) {
          res = SList(SSymbol("store"), res, toSMT(e), toSMT(BooleanLiteral(true)))
        }

        res

      case SubsetOf(ss, s) =>
        // a isSubset b   ==>   (a zip b).map(implies) == (* => true)
        val allTrue    = SList(SList(SSymbol("as"), SSymbol("const"), declareSort(s.getType)), SSymbol("true"))
        val mapImplies = SList(SList(extSym, SSymbol("map"), SSymbol("implies")), toSMT(ss), toSMT(s))

        SList(SSymbol("="), mapImplies, allTrue)

      case ElementOfSet(e, s) =>
        SList(SSymbol("select"), toSMT(s), toSMT(e))

      case SetDifference(a, b) =>
        // a -- b
        // becomes:
        // a && not(b)
        SList(SList(extSym, SSymbol("map"), SSymbol("and")), toSMT(a), SList(SList(extSym, SSymbol("map"), SSymbol("not")), toSMT(b)))
      case SetUnion(l, r) =>
        SList(SList(extSym, SSymbol("map"), SSymbol("or")), toSMT(l), toSMT(r))

      case SetIntersection(l, r) =>
        SList(SList(extSym, SSymbol("map"), SSymbol("and")), toSMT(l), toSMT(r))

      case _ =>
        super.toSMT(e)
  }

  def extractRawArray(s: SExpr)(implicit letDefs: Map[SSymbol, SExpr]): RawArrayValue = s match {
    case SList(List(SSymbol("define-fun"), a: SSymbol, SList(SList(List(arg, akind)) :: Nil), rkind, body)) =>
      val argTpe = sorts.toA(akind)
      val retTpe = sorts.toA(rkind)

      def extractCases(e: SExpr): (Map[Expr, Expr], Expr) = e match {
        case SList(SSymbol("ite") :: SList(SSymbol("=") :: `arg` :: k :: Nil) :: v :: e :: Nil) =>
          val (cs, d) = extractCases(e)
          (Map(fromSMT(k, argTpe) -> fromSMT(v, retTpe)) ++ cs, d)
        case e =>
          (Map(),fromSMT(e, retTpe))
      }

      val (cases, default) = extractCases(body)

      RawArrayValue(argTpe, cases, default)
    case _ =>
      unsupported("Unable to extract "+s)
  }
}
