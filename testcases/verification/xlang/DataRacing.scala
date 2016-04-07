import leon.lang._
import leon.lang.xlang._
import leon.util.Random

import leon.collection._

object DataRacing {
  
  case class SharedState(var i: Int)

  case class AtomicInstr(instr: (SharedState) => Unit)

  implicit def toInstr(instr: (SharedState) => Unit): AtomicInstr = AtomicInstr(instr)


  def execute(t1: List[AtomicInstr], t2: List[AtomicInstr], state: SharedState): Unit = (t1, t2) match {
    case (x::xs, y::ys) =>
      if(Random.nextBoolean) {
        x.instr(state)
        execute(xs, y::ys, state)
      } else {
        y.instr(state)
        execute(x::xs, ys, state)
      }
    case (Nil(), y::ys) =>
      y.instr(state)
      execute(Nil(), ys, state)
    case (x::xs, Nil()) =>
      x.instr(state)
      execute(xs, Nil(), state)
    case (Nil(), Nil()) => ()
  }

  def main(): Unit = {
    val state = SharedState(0)
    val t1 = List[AtomicInstr]((s: SharedState) => s.i = s.i + 1)
    val t2 = List[AtomicInstr]((s: SharedState) => s.i = s.i * 2)
    execute(t1, t2, state)
    assert(state.i == 2)
  }

}
