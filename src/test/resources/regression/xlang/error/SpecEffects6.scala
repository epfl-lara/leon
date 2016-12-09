import leon.lang._

object SpecEffects6 {

  def bar(): Unit = {
    var i = 0
    assert({
      i += 1
      i == 1
    })
  }

}
