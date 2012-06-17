import leon.Utils._

object Arithmetic {

  /* VSTTE 2008 - Dafny paper */
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

  /* VSTTE 2008 - Dafny paper */
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

  /* VSTTE 2008 - Dafny paper */
  def addBuggy(x : Int, y : Int): Int = ({
    var r = x
    if(y < 0) {
      var n = y
      (while(n != 0) {
        r = r + 1
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

  def sum(n: Int): Int = {
    require(n >= 0)
    var r = 0
    var i = 0
    (while(i < n) {
      i = i + 1
      r = r + i
    }) invariant(r >= i && i >= 0 && r >= 0)
    r
  } ensuring(_ >= n)

}
