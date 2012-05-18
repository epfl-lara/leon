import leon.Utils._

object Arith {

  def mult(x : Int, y : Int): Int = ({
    var r = 0
    if(y < 0) {
      var n = y
      (while(n != 0) {
        r = r - x
        n = n + 1
      }) invariant(r == x * (y - n) && 0 <= -n)
    } else {
      var n = y
      (while(n != 0) {
        r = r + x
        n = n - 1
      }) invariant(r == x * (y - n) && 0 <= n)
    }
    r
  }) ensuring(_ == x*y)

  def add(x : Int, y : Int): Int = ({
    var r = x
    if(y < 0) {
      var n = y
      (while(n != 0) {
        r = r - 1
        n = n + 1
      }) invariant(r == x + y - n && 0 <= -n)
    } else {
      var n = y
      (while(n != 0) {
        r = r + 1
        n = n - 1
      }) invariant(r == x + y - n && 0 <= n)
    }
    r
  }) ensuring(_ == x+y)

}
