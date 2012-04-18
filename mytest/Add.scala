import leon.Utils._

/* VSTTE 2008 - Dafny paper */

object Add {

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
