import leon.lang._
import leon.annotation._

object ExprComp {

  // Values
  sealed abstract class Whatever
  case class Value(v : Int) extends Whatever

  // Operations
  sealed abstract class BinOp
  case class Plus() extends BinOp
  case class Times() extends BinOp

  // Expressions
  sealed abstract class Expr
  case class Constant(v : Value) extends Expr
  case class Binary(exp1 : Expr, op : BinOp, exp2 : Expr) extends Expr

  def exprSize(e: Expr) : Int = (e match {
    case Constant(_) => 1
    case Binary(e1, _, e2) => 1 + exprSize(e1) + exprSize(e2)
  }) ensuring(_ >= 1)

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

  def progSize(p: Program) : Int = (p match {
    case EProgram() => 0
    case NProgram(_, r) => 1 + progSize(r)
  }) ensuring(_ >= 0)

  // Value stack

  sealed abstract class ValueStack
  case class EStack() extends ValueStack
  case class NStack(v : Value, rest : ValueStack) extends ValueStack

  def stackSize(vs: ValueStack) : Int = (vs match {
    case EStack() => 0
    case NStack(_, r) => 1 + stackSize(r)
  }) ensuring(_ >= 0)

  // Outcomes of running the program

  sealed abstract class Outcome
  case class Ok(v : ValueStack) extends Outcome
  case class Fail(v : ValueStack, i : Instruction) extends Outcome


  // Running programs on a given initial stack
  def run(p : Program, vs : ValueStack) : Outcome = p match {
    case EProgram() => Ok(vs)
    case NProgram(i,rest) => 
      val oRest = run(rest, vs)
      oRest match {
				case Fail(_,_) => oRest
				case Ok(vRest) =>
				  i match {
				    case PushVal(v) => Ok(NStack(v,vRest))
				    case ApplyBinOp(op) => vRest match {
	      				case EStack() => Fail(vRest, i)
	      				case NStack(v1,vs1) => vs1 match {
									case EStack() => Fail(vRest, i)
									case NStack(v2,vs2) => Ok(NStack(evalOp(v1,op,v2),vs2))
					      }
	    			}
	  			}
      }

  }


// --- this does not work; do not know why
  def property_trivial() : Boolean = {
		run(EProgram() , EStack() ) == Ok(EStack())
  } holds



  def run0(p : Program) = run(p, EStack())

  // Compiling expressions to programs

  def compile(e : Expr, acc : Program) : Program  = (e match {
    case Constant(v) => NProgram(PushVal(v), acc)
    case Binary(e1,op,e2) => NProgram(ApplyBinOp(op),compile(e2,compile(e1,acc)))
  }) // ensuring (res => (run(res, EStack()) == Ok(NStack(eval(e), EStack()))))
    // should be forall vs. ... vs ... instead of EStack() above.

  def compile0(e : Expr) : Program = compile(e, EProgram())

/*
  def property(e : Expr, acc : Program, vs : ValueStack) : Boolean = {
    require(exprSize(e) <= 1 && progSize(acc) <= 1 && stackSize(vs) <= 1)
    run(compile(e, acc), vs) == Ok(NStack(eval(e), vs))
  } holds

*/



/// --- here it goes bad
  def property0() : Boolean = {
    val e = Binary(Constant(Value(3)), Plus(), Constant(Value(5)))
    val vs = EStack()
    val acc = EProgram()
    run(compile(e, acc), vs) == Ok(NStack(eval(e), vs))
  } //holds


//this induction should work (at least on paper it goes ok)
  @induct
  def property_general(e: Expr, prog:Program) : Boolean = {
    val vs = EStack()
    val result = run(prog, vs)
    result match{
			case Ok(vv) => run(compile(e, prog), vs) == Ok(NStack(eval(e), vv))
			case _ => true
    }
  } holds




  @induct
  def property1(e: Expr) : Boolean = {
    val vs = EStack()
    run(compile(e, EProgram()), vs) == Ok(NStack(eval(e), vs))
  } holds

//  def property2(e: Expr, vs: ValueStack) : Boolean = {
//    run(compile(e, EProgram()), vs) == Ok(NStack(eval(e), vs))
//  } holds
/*
  def main(args : Array[String]) = {
    val e = Binary(Constant(Value(100)), Times(), Binary(Constant(Value(3)), Plus(), Constant(Value(5))))
    val vs = EStack()
    val acc = EProgram()
    println(compile(e,acc))
    println(run(compile(e, acc), vs))
    println(Ok(NStack(eval(e), vs)))
    assert(property(e,acc,vs))
  }
  */

}
