import leon.lang._
import leon.lang.Option
import leon.collection._
import leon.annotation._
import leon.proof._
import leon.lang.synthesis._

object TinyCertifiedCompiler {
  abstract class ByteCode[A]
  case class Load[A](c: A) extends ByteCode[A] // loads a constant in to the stack
  case class OpInst[A]() extends ByteCode[A]

  abstract class ExprTree[A]
  case class Const[A](c: A) extends ExprTree[A]
  case class Op[A](e1: ExprTree[A], e2: ExprTree[A]) extends ExprTree[A]

  def compile[A](e: ExprTree[A]): List[ByteCode[A]] = {
    e match {
      case Const(c) =>
        Cons(Load(c), Nil[ByteCode[A]]())
      case Op(e1, e2) =>
        (compile(e1) ++ compile(e2)) ++ Cons(OpInst(), Nil[ByteCode[A]]())
    }
  }

  def op[A](x: A, y: A): A = {
    ???[A]
  }

  def run[A](bytecode: List[ByteCode[A]], S: List[A]): List[A] = {
    (bytecode, S) match {
      case (Cons(Load(c), tail), _) =>
        run(tail, Cons[A](c, S)) // adding elements to the head of the stack
      case (Cons(OpInst(), tail), Cons(x, Cons(y, rest))) =>
        run(tail, Cons[A](op(y, x), rest))
      case (Cons(_, tail), _) =>
        run(tail, S)
      case (Nil(), _) => // no bytecode to execute
        S
    }
  }

  def interpret[A](e: ExprTree[A]): A = {
    e match {
      case Const(c) => c
      case Op(e1, e2) =>
        op(interpret(e1), interpret(e2))
    }
  }

  def runAppendLemma[A](l1: List[ByteCode[A]], l2: List[ByteCode[A]], S: List[A]): Boolean = {
    // lemma
    (run(l1 ++ l2, S) == run(l2, run(l1, S))) because
      // induction scheme (induct over l1)
      (l1 match {
        case Nil() =>
          true
        case Cons(h, tail) =>
          (h, S) match {
            case (Load(c), _) =>
              runAppendLemma(tail, l2, Cons[A](c, S))
            case (OpInst(), Cons(x, Cons(y, rest))) =>
              runAppendLemma(tail, l2, Cons[A](op(y, x), rest))
            case (_, _) =>
              runAppendLemma(tail, l2, S)
            case _ =>
              true
          }
      })
  }.holds

  def compileInterpretEquivalenceLemma[A](e: ExprTree[A], S: List[A]): Boolean = {
    // lemma
    (run(compile(e), S) == interpret(e) :: S) because 
      // induction scheme
      (e match {
        case Const(c) =>
          true
        case Op(e1, e2) =>
          // lemma instantiation
          val c1 = compile(e1)
          val c2 = compile(e2)
          runAppendLemma((c1 ++ c2), Cons[ByteCode[A]](OpInst[A](), Nil[ByteCode[A]]()), S) &&
            runAppendLemma(c1, c2, S) &&
            compileInterpretEquivalenceLemma(e1, S) &&
            compileInterpretEquivalenceLemma(e2, Cons[A](interpret(e1), S))
      })
  } holds
}
