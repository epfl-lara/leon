import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object Foo {

  def listOp1(l: List[Int], i: Int) = {
    //Cons(i, (l-i))
    //Cons[Int](i, l).slice(0, i)
    ???[List[Int]]
  } ensuring { (res: List[Int]) =>
    ((l, i), res) passes {
      case (Nil(), 2) => Cons(2, Nil[Int]())
      case (Cons(1, Nil()), 2) => Cons(2, Cons(1, Nil()))
      case (Cons(1, Cons(2, Cons(3, Nil()))), 3) => Cons(3, Cons(1, Cons(2, Nil())))
    }
  }

}
