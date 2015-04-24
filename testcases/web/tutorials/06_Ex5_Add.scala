import leon.Utils._

/* VSTTE 2008 - Dafny paper */

/*
  Add the loop invariants so that Leon can verify this function.
*/

object Add {

  def add(x : BigInt, y : BigInt): BigInt = ({
    var r = x
    if(y < 0) {
      var n = y
      (while(n != 0) {
        r = r - 1
        n = n + 1
      }) //invariant(...)
    } else {
      var n = y
      (while(n != 0) {
        r = r + 1
        n = n - 1
      }) //invariant(...)
    }
    r
  }) ensuring(_ == x+y)

}
