object SpecEffects4 {

  def foo(): Int = {
    var x = 0
    assert({
      x = x+1
      x == 1
    })
    x = x+1
    x
  } ensuring(res => res == 2)

}
