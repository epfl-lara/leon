import leon.lang._
import leon.collection._
import leon.lang.synthesis._

object Lists {

  def safetail(l: List[Int]): List[Int] = choose { (res : List[Int]) =>
    (l, res) passes {
      case Cons(1, Cons(2, Cons(3, Cons(4, Nil())))) => Cons(2, Cons(3, Cons(4, Nil())))
      case Cons(2, Cons(3, Cons(4, Nil()))) => Cons(3, Cons(4, Nil()))
      case Nil() => Nil()
    }
  }

  def uniq(l: List[Int]): List[Int] = choose { (res : List[Int]) =>
    (l, res) passes {
      case Cons(1, Cons(1, Cons(1, Cons(2, Nil())))) => Cons(1, Cons(2, Nil()))
      case Cons(3, Cons(3, Cons(4, Nil()))) => Cons(3, Cons(4, Nil()))
      case Nil() => Nil()
    }
  }
}
