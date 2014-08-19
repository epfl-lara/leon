import leon.lang._
import leon.collection._
import leon.lang.synthesis._

object Lists {

  def safetail(l: List[Int]): List[Int] = choose { (res : List[Int]) =>
    passes(l, res)(Map(
      Cons(1, Cons(2, Cons(3, Cons(4, Nil())))) -> Cons(2, Cons(3, Cons(4, Nil()))),
      Cons(2, Cons(3, Cons(4, Nil()))) -> Cons(3, Cons(4, Nil())),
      Nil() -> Nil()
    ))
  }

  def uniq(l: List[Int]): List[Int] = choose { (res : List[Int]) =>
    passes(l, res)(Map(
      Cons(1, Cons(1, Cons(1, Cons(2, Nil())))) -> Cons(1, Cons(2, Nil())),
      Cons(3, Cons(3, Cons(4, Nil()))) -> Cons(3, Cons(4, Nil())),
      Nil() -> Nil()
    ))
  }
}
