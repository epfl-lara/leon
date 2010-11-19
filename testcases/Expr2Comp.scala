import funcheck.Utils._
import funcheck.Annotations._

object ExprComp {
  // Lists

  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  // Operations
  sealed abstract class BinOp
  case class Plus() extends BinOp
  case class Times() extends BinOp

  // Expressions
  sealed abstract class Expr
  case class Constant(v : Int) extends Expr
  case class Binary(exp1 : Expr, op : BinOp, exp2 : Expr) extends Expr

  def exprSize(e: Expr) : Int = (e match {
    case Constant(_) => 1
    case Binary(e1, _, e2) => 1 + exprSize(e1) + exprSize(e2)
  }) ensuring(_ >= 1)

  def evalOp(v1 : Int, op : BinOp, v2 : Int) : Int = op match {
    case Plus() => v1 + v2
    case Times() => v1 * v2
  }

  // Expression evaluation

  def eval(e : Expr) : Int = e match {
    case Constant(v) => v
    case Binary(e1,op,e2) => evalOp(eval(e1),op,eval(e2))
  }

  // Instructions

  sealed abstract class Instruction
  case class PushVal(v : Int) extends Instruction
  case class ApplyBinOp(op : BinOp) extends Instruction

  // Programs

  sealed abstract class Program
  case class EProgram() extends Program
  case class NProgram(first : Instruction, rest : Program) extends Program

  def progSize(p: Program) : Int = (p match {
    case EProgram() => 0
    case NProgram(_, r) => 1 + progSize(r)
  }) ensuring(_ >= 0)

  // Running programs on a given initial stack

  def run(p : Program, vs : List) : Int = p match {
    case EProgram() => vs match {
      case Nil() => -1
      case Cons(top,_) => top
    }
    case NProgram(PushVal(v),rest) => run(rest, Cons(v,rest))
    case NProgram(ApplyBinOp(op),rest) => 

run( Cons(evalOp(v1,op,v2),vs)

 vRest match {
	      case EStack() => Fail(vRest, i)
	      case NStack(v1,vs1) => vs1 match {
		case EStack() => Fail(vRest, i)
		case NStack(v2,vs2) => Ok(NStack(,vs2))
	      }
	    }
	  }

      val oRest = run(rest, vs)
      oRest match {
	case Fail(_,_) => oRest
	case Ok(vRest) =>
      }
  }
  def run0(p : Program) = run(p, EStack())
*/

  // Compiling expressions to programs

  def compile(e : Expr, acc : Program) : Program  = (e match {
    case Constant(v) => NProgram(PushVal(v), acc)
    case Binary(e1,op,e2) => compile(e1,compile(e2,NProgram(ApplyBinOp(op),acc)))
  }) // ensuring (res => (run(res, EStack()) == Ok(NStack(eval(e), EStack()))))
    // should be forall vs. ... vs ... instead of EStack() above.

  def compile0(e : Expr) : Program = compile(e, EProgram())

/*
  def property(e : Expr, acc : Program, vs : IntStack) : Boolean = {
    require(exprSize(e) <= 1 && progSize(acc) <= 1 && stackSize(vs) <= 1)
    run(compile(e, acc), vs) == Ok(NStack(eval(e), vs))
  } holds

  def property0() : Boolean = {
    val e = Binary(Constant(3), Plus(), Constant(5))
    val vs = EStack()
    val acc = EProgram()
    run(compile(e, acc), vs) == Ok(NStack(eval(e), vs))
  } holds

  @induct
  def property1(e: Expr) : Boolean = {
    val vs = EStack()
    run(compile(e, EProgram()), vs) == Ok(NStack(eval(e), vs))
  } holds
*/

//  def property2(e: Expr, vs: IntStack) : Boolean = {
//    run(compile(e, EProgram()), vs) == Ok(NStack(eval(e), vs))
//  } holds

  def main(args : Array[String]) = {
    val e = Binary(Constant(100), Times(), Binary(Constant(3), Plus(), Constant(5)))
    val acc = EProgram()
    println(compile(e,acc))
    println(eval(e))
    //println(run(compile(e, acc), vs))
    //println(Ok(NStack(eval(e), vs)))
    //assert(property(e,acc,vs))
  }
}
