import leon.annotation._
import leon.collection._
import leon.lang._

object Overlapping {

  def overlapped[A](xs: List[A]) = {
    require { xs.isInstanceOf[Cons[A]] }

    xs match {
      case Cons(x1, Cons(x2, xs)) => true
      case Cons(x1, xs) => true
      case _ => false
    }
  }.holds

}
