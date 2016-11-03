import leon.lang._

object SpecEffects5 {

  def foo(n: Int): Int = {
    var x = 0
    (while(x < n) {
      ()
    }) invariant({
      x = x+1
      x >= 0 && x <= n
    })
    x
  } ensuring(res => res == n)

}
