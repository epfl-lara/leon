object ExprComp {

  // Values
  case class Value(v : Int)

  // Operations
  sealed abstract class BinOp
  case class Plus() extends BinOp
  case class Times() extends BinOp

  // Expressions
  sealed abstract class Expr
  case class Constant(v : Value) extends Expr
  case class Binary(exp1 : Expr, op : BinOp, exp2 : Expr) extends Expr

  def evalOp(v1 : Value, op : BinOp, v2 : Value) : Value = op match {
    case Plus() => Value(v1.v + v2.v)
    case Times() => Value(v1.v * v2.v)
  }

  // Expression evaluation

  def eval(e : Expr) : Value = e match {
    case Constant(v) => v
    case Binary(e1,op,e2) => evalOp(eval(e1),op,eval(e2))
  }

  // Instructions

  sealed abstract class Instruction
  case class PushVal(v : Value) extends Instruction
  case class ApplyBinOp(op : BinOp) extends Instruction

  // Programs

  sealed abstract class Program
  case class EProgram() extends Program
  case class NProgram(first : Instruction, rest : Program) extends Program

  // Value stack

  sealed abstract class ValueStack
  case class EStack() extends ValueStack
  case class NStack(v : Value, rest : ValueStack) extends ValueStack

  // Outcomes of running the program

  sealed abstract class Outcome
  case class Ok(v : ValueStack) extends Outcome
  case class Fail() extends Outcome

  // Running programs on a given initial stack
  def run(p : Program, vs : ValueStack) : Outcome = p match {
    case EProgram() => Ok(vs)
    case NProgram(i,rest) => i match {
      case PushVal(v) => run(rest, NStack(v,vs))
      case ApplyBinOp(op) => vs match {
	case EStack() => Fail()
	case NStack(v1,vs1) => vs1 match {
	  case EStack() => Fail()
	  case NStack(v2,vs2) => Fail() // should be: run(rest, NStack(evalOp(v1,op,v2),vs2))
	}
      }
    }
  }

  def run0(p : Program) = run(p, EStack())

  // Compiling expressions to programs
  def compile(e : Expr, acc : Program) : Program = e match {
    case Constant(v) => NProgram(PushVal(v), acc)
    case Binary(e1,op,e2) => NProgram(ApplyBinOp(op),compile(e2,compile(e1,acc)))
  }

  def compile0(e : Expr) : Program = compile(e, EProgram())

  def property(e : Expr, acc : Program, vs : ValueStack) : Boolean = {
    run(compile(e, acc), vs) == Ok(NStack(eval(e), vs))
  } ensuring (res => res)

  def main(args : Array[String]) = {
    val e = Binary(Constant(Value(3)), Plus(), Constant(Value(5)))
    val vs = EStack()
    val acc = EProgram()
    println(run(compile(e, acc), vs))
    println(Ok(NStack(eval(e), vs)))
    println(property(e,acc,vs))
  }
}
