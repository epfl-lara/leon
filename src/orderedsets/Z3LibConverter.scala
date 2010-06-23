package orderedsets

import AST._
import Primitives._
import z3.scala._
import scala.collection.mutable.ArrayBuffer

abstract sealed class Z3Output;
case class Z3Failure(e: Exception) extends Z3Output
case object Unsat extends Z3Output;
case class Sat(deleteModel: (() => Unit), boolAssignments: (Symbol => Boolean), intAssignments: (Symbol => Int)) extends Z3Output;

class MyZ3Context {
  private var z3 = new Z3Context((new Z3Config).setParamValue("MODEL", "true"))
  private val intType = z3.mkIntSort
  private val boolType = z3.mkBoolSort

  private var debug_stack = List(new ArrayBuffer[Formula])

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

  def impose(form: Formula) {
    debug_stack.head += form
    z3.assertCnstr(mkAST(form))
  }

  def push {
    debug_stack ::= new ArrayBuffer[Formula]
    z3.push
  }

  def pop {
    assert(stackSize > 1)
    z3.pop(1)
    debug_stack = debug_stack.tail
  }

  def delete {
    z3.delete
    z3 = null
  }

  def stackSize = debug_stack.size

  def printStack {
    val size = stackSize
    for ((buf, i) <- debug_stack.zipWithIndex) {
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
      case (None,_) => Z3Failure(new Exception("There was an error with Z3."))
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

object Z3LibConverter {
  /*
  def getConstrs(formula: Formula, z3: Z3Context) = {

    val intType = z3.mkIntSort
    val boolType = z3.mkBoolSort

    def termToZ3Term(trm: Term): Z3AST = trm match {
        case TermVar(name) => name.getZ3Symb(z3)
        case Lit(IntLit(v)) => z3.mkInt(v, intType)
        case Op(ADD, trmLst) => z3.mkAdd((trmLst map termToZ3Term).toArray : _ *)
        case Op(SUB, List(t1, t2)) => z3.mkSub(termToZ3Term(t1), termToZ3Term(t2))
        case Op(MUL, trmLst) => z3.mkMul((trmLst map termToZ3Term).toArray : _ *)
        case Op(ITE(f), List(t1, t2)) => z3.mkITE( formulaToZ3Form(f), termToZ3Term(t1), termToZ3Term(t2))
        case Op(MIN, t1 :: t2 :: rest) => {
            val subExpr = termToZ3Term(Op(MIN, t2 :: rest))
            val thisExpr = termToZ3Term(t1)
            z3.mkITE(z3.mkLT(thisExpr, subExpr), thisExpr, subExpr)
          }
        case Op(MIN, t1 :: Nil) => termToZ3Term(t1)
        case Op(MAX, t1 :: t2 :: rest) => {
            val subExpr = termToZ3Term(Op(MAX, t2 :: rest))
            val thisExpr = termToZ3Term(t1)
            z3.mkITE(z3.mkGT(thisExpr, subExpr), thisExpr, subExpr)
          }
        case Op(MAX, t1 :: Nil) => termToZ3Term(t1)
        case _ => throw (new IllegalTerm(trm))
      }


    def formulaToZ3Form(f: Formula): Z3AST = f match {
        case True => z3.mkTrue
        case False => z3.mkFalse
        case PropVar(v) => v.getZ3Symb(z3)
        case And(fs) => z3.mkAnd((fs map formulaToZ3Form).toArray : _ *)
        case Or(fs) => z3.mkOr((fs map formulaToZ3Form).toArray : _ *)
        case Not(form) => z3.mkNot(formulaToZ3Form(form))
        case Predicate(op: IntLogical, List(t1, t2)) => opToZ3Predicate(op, t1, t2)
        case _ => throw (new IllegalTerm(f))
      }
      
      formulaToZ3Form(formula)
  }

  def queryIsStillSAT(z3: Z3Context) : Boolean = {
    val result: java.lang.Boolean = z3.check()
    if(result == null) 
        throw (new Exception("There was an error with Z3."))
    else {
      result.booleanValue
    }
  }

  def queryGetModel(z3: Z3Context) : Z3Output = {
    val model = z3.mkModel
    val result: java.lang.Boolean = z3.checkAndGetModel(model)

    if (result == null) {
        Z3Failure(new Exception("There was an error with Z3."))
      } else if (result.booleanValue) {
        def boolAssigns(x:Symbol) = {
               val v = model.evalAsBool(x.getZ3Symb(z3))
               if(v==null) false else v.booleanValue
        }
        def intAssigns(x:Symbol) = {
               val v = model.evalAsInt(x.getZ3Symb(z3))
               if(v==null) 0 else v.intValue
        }
        def delete() = {println("****DELETED!!!"); model.delete}
        Sat(delete, boolAssigns, intAssigns)
      } else {
        model.delete
        Unsat
      }
    }*/

  //  def isSat(form: Formula) : Z3Output = {
  //    val z3 = new Z3Context((new Z3Config).setParamValue("MODEL", "true"))
  //    val response = isSat(form, z3)
  //    z3.delete
  //    response
  //  }

  /*  def isSat(form: Formula, z3 : Z3Context) : Z3Output = {

  val startTime = Calendar.getInstance().getTimeInMillis()
  val intType = z3.mkIntSort
  val boolType = z3.mkBoolSort

  val intVarsInForm = ASTUtil.intvars(form).toList
  val boolVarsInForm = ASTUtil.propvars(form).toList

  // val intZ3ValMap = Map() ++ intVarsInForm.map { (x:String) => (x -> z3.mkConst(z3.mkStringSymbol(x), intType)) }
  // val boolZ3ValMap = Map() ++ boolVarsInForm.map { (x:String) => (x -> z3.mkConst(z3.mkStringSymbol(x), boolType)) }

  val constr = getConstrs(form, z3);
  z3.assertCnstr(constr)

  queryGetModel(z3)
  }*/
}

object Z3LibConverterTester {
  def main(args: Array[String]) = {
    val a = Symbol("a")
    val b = Symbol("b")
    val c = Symbol("c")
    val d = Lit(IntLit(3))
    val pSymb = Symbol.beta(1, TermVar(Symbol.freshSet))
    val p = PropVar(pSymb)

    val form = (a * d - c === 0) && (c === Op(ITE(p), TermVar(a) :: TermVar(b) :: Nil))
    println("Formula = ");
    form.print;
    println("Int vars = " + ASTUtil.intvars(form));
    // println("Constraint = " + Z3LibConverter.getConstrs(form, List(a, b, c).map(_.toString), Nil, (new Z3Context((new Z3Config).setParamValue("MODEL", "true")))))

    val z3 = new MyZ3Context

    val constr = List(
      a === Op(MIN, List(TermVar(b), TermVar(c))),
      a + 1 === b,
      c < a,
      c < b,
      p implies ((a === 1) && (c === 2)),
      p
      )
    println("\n\nIncredible Per clause testing example:")
    for (cstr <- constr) {
      z3.push
      z3.impose(cstr)
      z3.printStack
      if (z3.isStillSAT) {
        println("True")
      } else {
        println("False")
        z3.pop
      }
    }
    z3.delete
  }
}
