import leon.lang._
import leon.lang.synthesis._

object DrSuter {

  abstract class List
  case class Nil() extends List
  case class Cons(head : Int, tail : List) extends List

  def myChoose(a : List) : (Int,Int,List) = {
    choose { (x: Int, y: Int, ys: List) =>
      Cons(x, Cons(y, ys)) == a && x == y ||
      Cons(x, ys) == a          && x < 0
    }
  }
}
