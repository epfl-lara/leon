import leon.lang._
import leon.lang.Option
import leon.collection._
import leon.annotation._

object TinyCertifiedCompiler {

  abstract class ByteCode
  case class Load(c: BigInt) extends ByteCode // loads a constant in to the stack
  case class OpInst() extends ByteCode

  abstract class ExprTree
  case class Const(c: BigInt) extends ExprTree
  case class OP(e1: ExprTree, e2: ExprTree) extends ExprTree

  def compile(e: ExprTree): List[ByteCode] = {
    e match {
      case Const(c) =>
        Cons(Load(c), Nil[ByteCode]())
      case OP(e1, e2) =>
        (compile(e1) ++ compile(e2)) ++ Cons(OpInst(), Nil[ByteCode]())
    }
  }

  def op(x: BigInt, y: BigInt) : BigInt = {
    x + y    
  }

  def run(bytecode: List[ByteCode], S: Option[List[BigInt]]) : Option[List[BigInt]] = {
    (bytecode, S) match {
      case (Cons(Load(c), tail), Some(stack)) =>
        run(tail, Some(Cons(c, stack))) // adding elements to the head of the stack
      case (Cons(OpInst(), tail), Some(Cons(x, Cons(y, rest)))) =>
        run(tail, Some(Cons(op(x, y), rest)))
      case (Nil(), _) => // no bytecode to execute
        S
      case _ =>
        // here, we have encountered a runtime error, so we return None to signal error
        None[List[BigInt]]
    }
  }

  def interpret(e: ExprTree) : BigInt = {
    e match {
      case Const(c) => c
      case OP(e1, e2) =>
        op(interpret(e1), interpret(e2))
    }
  }

  def runAppendLemma(l1: List[ByteCode], l2: List[ByteCode], S: Option[List[BigInt]]) : Boolean = {
    // lemma
    run(l1 ++ l2, S) == run(l2, run(l1, S)) &&
    // induction scheme (induct over l1)
    (l1 match {
      case Nil() =>
        true
      case Cons(h, tail) =>
        (h, S) match {
          case (Load(c), Some(stk)) =>
            runAppendLemma(tail, l2, Some(Cons(c, stk)))
          case (OpInst(), Some(Cons(x, Cons(y, rest)))) =>
            runAppendLemma(tail, l2, Some(Cons(op(x, y), rest)))
          case _ =>
            true
        }
    })
  } holds

  def compileInterpretEquivalenceLemma(e: ExprTree, S: Option[List[BigInt]]) : Boolean = {
    S match {
      case None() => true
      case Some(stk) =>
        // lemma
        (run(compile(e), S) match {
          case None() => true // here, there was a run-time error
          case Some(rstk) =>
            rstk == Cons[BigInt](interpret(e), stk)
        }) &&
          // induction scheme
          (e match {
            case Const(c) =>
              true
            case OP(e1, e2) =>
              // lemma instantiation
              val c1 = compile(e1)
              val c2 = compile(e2)
              runAppendLemma((c1 ++ c2), Cons(OpInst(), Nil[ByteCode]()), S) &&
                runAppendLemma(c1, c2, S) &&
              compileInterpretEquivalenceLemma(e1, S) &&
                compileInterpretEquivalenceLemma(e2, Some(Cons[BigInt](interpret(e1), stk)))
          })
    }
  } holds
}
