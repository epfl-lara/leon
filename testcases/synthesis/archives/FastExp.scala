import leon.annotation._
import leon.lang.synthesis._
import leon.lang._

object FastExp {

  def test(a : Int) : Int = {
    val j1 = choose((k: Int) => 2*k == a)
    val j2 = choose((k: Int) => 2*k + 1 == a)
    j1 + j2
  }

  //def fp(m : Int, b : Int, i : Int) : Int = i match {
  //  case 0         => m
  //  case 2 * j     => fp(m, b*b, j)
  //  case 2 * j + 1 => fp(m*b, b*b, j)
  //}

  //def pow(base: Int, p: Int) = {
  //  fp(1, base, p)
  //}

}
