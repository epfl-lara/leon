import leon.Utils._

object FastExp {

  def fp(m : Int, b : Int, i : Int) : Int = i match {
    case 0         => m
    case 2 * j     => fp(m, b*b, j)
    case 2 * j + 1 => fp(m*b, b*b, j)
  }

  def pow(base: Int, p: Int) = {
    fp(1, base, p)
  }

}
