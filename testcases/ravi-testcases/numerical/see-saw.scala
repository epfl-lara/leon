import leon.lang.invariantLang._

object SeeSaw {
  def s(x: Int, y: Int, z: Int): Int = {
    require(y >= 0)

    if (x >= 100) {
      y
    } else if (x <= z) { //some condition
      s(x + 1, y + 2, z)
    } else if (x <= z + 9) { //some condition
      s(x + 1, y + 3, z)
    } else {
      s(x + 2, y + 1, z)
    }
  } ensuring (res => (100 - x <= 2 * res))
  //template((a, b, c, d) => (a*res + b*x + c*y + d <= 0) 
} 
//will this terminate ?
//Does the invariant hold ?
//can it be proven by induction ?










//inductive generalization (100 - x  <= 2*(res - y))