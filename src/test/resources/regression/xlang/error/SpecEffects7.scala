import leon.lang._

object SpecEffects7 {

  def foo(): Unit = {
    var i = 0
    def incI = {
      i += 1
      i
    }
    assert(incI == 1)
  }

}
