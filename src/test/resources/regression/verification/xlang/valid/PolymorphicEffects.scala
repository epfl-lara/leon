import leon.lang._

object PolymorphicEffects {

  case class Effect[E: Mutable](e: E)
  
  def hof[E: Mutable](f: (Int, Effect[E]) => Int, e: Effect[E]): Int = f(1, e)

  case class State(var x1: Int, var x2: Int, var x3: Int)

  def incAndAdd(x: Int, effect: Effect[State]): Int = {
    effect.e.x1 += 1
    effect.e.x2 += 1
    effect.e.x3 += 1
    effect.e.x1 + effect.e.x2 + effect.e.x3
  }

  def test = {
    val state = State(10, 12, 14)
    val res = hof(incAndAdd, Effect(state))
    assert(state.x1 == 11)
    assert(state.x2 == 13)
    assert(state.x3 == 15)
    assert(res == 11 + 13 + 15)
  }

}
