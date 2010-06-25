package orderedsets

import AST._
import Primitives._
import z3.scala._
import scala.collection.mutable.ArrayBuffer
import Symbol._

abstract sealed class Z3Output
case object Unsat extends Z3Output
case class Z3Failure(e: Exception) extends Z3Output
case class Sat(deleteModel: (() => Unit), boolAssignments: (Symbol => Boolean), intAssignments: (Symbol => Int)) extends Z3Output;

class MyZ3Context {
  private var z3 = new Z3Context((new Z3Config).setParamValue("MODEL", "true"))
  private val intType = z3.mkIntSort
  private val boolType = z3.mkBoolSort

  private var debugStack = List(new ArrayBuffer[Formula])

  private implicit def sym2z3ast(sym: Symbol): Z3AST = sym toZ3sym this

  // TODO 'leaks' a Z3AST object ..
  def mkSym(sym: Symbol) = sym.tpe match {
    case IntType => z3.mkConst(z3.mkStringSymbol(sym.name), intType)
    case BoolType => z3.mkConst(z3.mkStringSymbol(sym.name), boolType)
    case _ => error("Set symbol being passed to Z3!")
  }

  private def mkAST(form: Formula): Z3AST = form match {
    case True => z3.mkTrue
    case False => z3.mkFalse
    case PropVar(sym) => sym
    case And(fs) => z3.mkAnd((fs map mkAST).toArray: _ *)
    case Or(fs) => z3.mkOr((fs map mkAST).toArray: _ *)
    case Not(form) => z3.mkNot(mkAST(form))
    case Predicate(op: IntLogical, List(t1, t2)) => logicalOp(op, mkAST(t1), mkAST(t2))
    case _ => throw IllegalTerm(form)
  }

  private def logicalOp(op: IntOperand, t1: Z3AST, t2: Z3AST): Z3AST = op match {
    case LT => z3.mkLT(t1, t2)
    case LE => z3.mkLE(t1, t2)
    case EQ => z3.mkEq(t1, t2)
    case GT => z3.mkGT(t1, t2)
    case GE => z3.mkGE(t1, t2)
    case NE => z3.mkDistinct(t1, t2)
  }

  private def mkAST(term: Term): Z3AST = term match {
    case TermVar(sym) => sym
    case Lit(IntLit(v)) => z3.mkInt(v, intType)
    case Op(ADD, ts) => z3.mkAdd((ts map mkAST).toArray: _ *)
    case Op(SUB, List(t1, t2)) => z3.mkSub(mkAST(t1), mkAST(t2))
    case Op(MUL, ts) => z3.mkMul((ts map mkAST).toArray: _ *)
    case Op(ITE(f), List(t1, t2)) => z3.mkITE(mkAST(f), mkAST(t1), mkAST(t2))
    case Op(MIN, List(t1)) => mkAST(t1)
    case Op(MAX, List(t1)) => mkAST(t1)
    case Op(MIN, t1 :: ts) => {
      val subExpr = mkAST(Op(MIN, ts))
      val thisExpr = mkAST(t1)
      z3.mkITE(z3.mkLT(thisExpr, subExpr), thisExpr, subExpr)
    }
    case Op(MAX, t1 :: ts) => {
      val subExpr = mkAST(Op(MAX, ts))
      val thisExpr = mkAST(t1)
      z3.mkITE(z3.mkGT(thisExpr, subExpr), thisExpr, subExpr)
    }
    case _ => throw IllegalTerm(term)
  }

  /* Interface */

  def impose(form: Formula) {
    val nnfForm = NormalForms.nnf(form)
    debugStack.head += nnfForm
    z3.assertCnstr(mkAST(nnfForm))
  }

  def push {
    debugStack ::= new ArrayBuffer[Formula]
    z3.push
  }

  def pop {
    assert(stackSize > 1)
    z3.pop(1)
    debugStack = debugStack.tail
  }

  def delete {
    z3.delete
    z3 = null
  }

  def stackSize = debugStack.size

  def printStack {
    val size = stackSize
    for ((buf, i) <- debugStack.zipWithIndex) {
      print("[Level " + (size - i) + "] ")
      NormalForms.nnf(And(buf.toList)).print
      /*for (form <- buf) {
        form.print
      }*/
    }
  }

  def isStillSAT: Boolean = z3.check() match {
    case None => throw new Exception("There was an error with Z3.")
    case Some(x) => x
  }

  def getModel: Z3Output = {
    z3.checkAndGetModel() match {
      case (None, _) => Z3Failure(new Exception("There was an error with Z3."))
      case (Some(true), model) => {
        def boolAssigns(sym: Symbol) = model.evalAsBool(sym) match {
          case None => false
          case Some(v) => v
        }
        def intAssigns(sym: Symbol) = model.evalAsInt(sym) match {
          case None => 0
          case Some(v) => v
        }
        def delete() {model.delete}
        Sat(delete, boolAssigns, intAssigns)
      }
      case (Some(false), _) => Unsat
    }
  }
}
