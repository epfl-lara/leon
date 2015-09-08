import leon._
import leon.annotation._
import leon.collection._
import leon.lang._

object Casts {

  def check1[A](xs: List[A]) =
    ((xs.size >= 1) || xs.asInstanceOf[Cons[A]].t == Nil[A]()).holds

  def check2[A](xs: List[A]) =
    ((xs.size != 1) || xs.asInstanceOf[Cons[A]].t == Nil[A]()).holds

}
