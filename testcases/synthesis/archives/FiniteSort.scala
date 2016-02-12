import leon.lang._
import leon.lang.synthesis._

object FiniteSort {

  def sort3(x1: Int, x2: Int, x3: Int): (Int, Int, Int) = {
    choose((z1: Int, z2: Int, z3: Int) => 
      z1 <= z2 && z2 <= z3 && (
        (z1 == x1 && z2 == x2 && z3 == x3) ||
        (z1 == x1 && z2 == x3 && z3 == x2) ||
        (z1 == x2 && z2 == x1 && z3 == x3) ||
        (z1 == x2 && z2 == x3 && z3 == x1) ||
        (z1 == x3 && z2 == x1 && z3 == x2) ||
        (z1 == x3 && z2 == x2 && z3 == x1)
      )
    )
  }

}
