import leon.lang._
import leon.lang.xlang._
import leon.util.Random

import leon.collection._

object DataRacing {
  
  case class SharedState(var i: Int)

  case class AtomicInstr(instr: (SharedState) => Unit)

  implicit def toInstr(instr: (SharedState) => Unit): AtomicInstr = AtomicInstr(instr)

  abstract class Runnable
  case class RunnableCons(instr: AtomicInstr, tail: Runnable) extends Runnable
  case class RunnableNil() extends Runnable

  def execute(t1: Runnable, t2: Runnable, state: SharedState)(implicit randomState: Random.State): Unit = (t1, t2) match {
    case (RunnableCons(x,xs), RunnableCons(y,ys)) =>
      if(Random.nextBoolean) {
        x.instr(state)
        execute(xs, RunnableCons(y,ys), state)
      } else {
        y.instr(state)
        execute(RunnableCons(x,xs), ys, state)
      }
    case (RunnableNil(), RunnableCons(y,ys)) =>
      y.instr(state)
      execute(RunnableNil(), ys, state)
    case (RunnableCons(x,xs), RunnableNil()) =>
      x.instr(state)
      execute(xs, RunnableNil(), state)
    case (RunnableNil(), RunnableNil()) => ()
  }

  //z3 finds counterexample in 0.5
  //cvc4 needs 130 seconds
  def main(): Int = {
    implicit val randomState = Random.newState
    val state = SharedState(0)
    val t1 = RunnableCons((s: SharedState) => s.i = s.i + 1, RunnableNil())
    val t2 = RunnableCons((s: SharedState) => s.i = s.i * 2, RunnableNil())
    execute(t1, t2, state)
    state.i
  } ensuring(_ == 2)

}
