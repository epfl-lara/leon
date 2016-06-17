import leon.lang._
import leon.annotation._

object SFuns {

  case class State(var x: BigInt)

  case class SFun(state: State, f: (BigInt, State) => BigInt) {

    def apply(x: BigInt): BigInt = f(x, state)
  }


  def counter(init: BigInt): SFun = {
    val state = State(init)
    val closure = SFun(state, (_, s) => { //TODO: should reject `state` in constructor, shared reference!
      s.x += 1
      (s.x - 1)
    })
    closure
  }


  def test(init: BigInt): Unit = {
    val gen = counter(init)
    val x1 = gen(0)
    assert(x1 == init)
    val x2 = gen(0)
    assert(x2 == init+1)
    val x3 = gen(0)
    assert(x3 == init+2)
  }


}
