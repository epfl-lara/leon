import leon.lang._
import leon.lang.xlang._
import leon.util.Random

import leon.collection._

object DataRacing {
  
  case class SharedState(var r1: Int, var r2: Int, var m: Int)

  case class AtomicInstr(instr: (SharedState) => Unit)

  implicit def toInstr(instr: (SharedState) => Unit): AtomicInstr = AtomicInstr(instr)

  case class Thread(var instrs: List[AtomicInstr]) {
    def terminated: Boolean = instrs.isEmpty
    def executeOneStep(state: SharedState): Unit = {
      require(!terminated)
      val Cons(head, tail) = instrs
      head.instr(state)
      instrs = tail
    }
  }

  //can we use a real thread, with mutable list of operations?
  //abstract class Runnable {
  //  def terminated: Boolean = this match {
  //    case RunnableNil() => true
  //    case _ => false
  //  }
  //  def executeOneStep(state: SharedState): Runnable = {
  //    require(!terminated)
  //    val RunnableCons(instr, rest) = this
  //    instr.instr(state)
  //    rest 
  //  }
  //}
  //case class RunnableCons(instr: AtomicInstr, tail: Runnable) extends Runnable
  //case class RunnableNil() extends Runnable

  //with the mutable thread, we would be able to check ensuring _.terminated
  def execute(t1: Thread, t2: Thread, state: SharedState)(implicit randomState: Random.State): Unit = {
    while(!t1.terminated || !t2.terminated) {
      if(t1.terminated) {
        t2.executeOneStep(state)
      } else if(t2.terminated) {
        t1.executeOneStep(state)
      } else {
        if(Random.nextBoolean) {
          t1.executeOneStep(state)
        } else {
          t2.executeOneStep(state)
        }
      }
    }
  } ensuring(_ => t1.terminated && t2.terminated)

  //z3 finds counterexample in 0.5
  //cvc4 needs 130 seconds
  //def main(): Int = {
  //  implicit val randomState = Random.newState
  //  val state = SharedState(0)
  //  val t1 = Thread(List((s: SharedState) => s.i = s.i + 1))
  //  val t2 = Thread(List((s: SharedState) => s.i = s.i * 2))
  //  execute(t1, t2, state)
  //  state.i
  //} ensuring(_ == 2)

  def main(): Unit = {
    implicit val randomState = Random.newState
    val state = SharedState(0,0,0)
    val t1 = Thread(List(
      (s: SharedState) => s.r1 = s.m,
      (s: SharedState) => s.r1 = s.r1 + 1,
      (s: SharedState) => s.m = s.r1
    ))
    val t2 = Thread(List(
      (s: SharedState) => s.r2 = s.m,
      (s: SharedState) => s.r2 = s.r2 + 1,
      (s: SharedState) => s.m = s.r2
    ))
    execute(t1, t2, state)
    assert(state.m == 2)
  }
}
