import leon.lang._
import leon.annotation._
import leon.collection._

object Relations {
  sealed case class G[A](domain: List[A])

  def forall[A](p: A => Boolean)(implicit g: G[A]) : Boolean = {
    g.domain.forall(p)
  }
  def exists[A](p: A => Boolean)(implicit g: G[A]) : Boolean = {
    g.domain.exists(p)
  }

  def circ[A](r1: ((A,A)) ⇒ Boolean, r2: ((A,A)) ⇒ Boolean)(implicit g: G[A]) : (((A,A)) => Boolean) = {
    case (x,z) => exists((y:A) => r1(x,y) && r2(y,z))
  }

  def eq[A](s1: A ⇒ Boolean, s2: A ⇒ Boolean)(implicit g: G[A]): Boolean = {
    forall((x:A) => s1(x)==s2(x))
  }

  def setOf[A](l: List[A]): (A => Boolean) = (l.contains(_))

  def test(r1: ((Int,Int))  => Boolean, r2: ((Int,Int))  => Boolean): Boolean = {
    implicit val g1: G[Int] = G[Int](List(1,2))
    implicit val g2: G[(Int,Int)] = G(List(1 -> 1, 1 -> 2, 2 -> 2, 2 -> 1, 3 -> 2, 3 -> 1))
    //val r1: ((Int,Int))  => Boolean = setOf(List(1 -> 2, 2 -> 3, 3 -> 1))
    //val r2: ((Int,Int))  => Boolean = setOf(List(1 -> 1, 2 -> 3, 3 -> 2))
    val commutative = 
      eq(circ(r1, r2), circ(r2, r1))

    val r3: ((Int,Int))  => Boolean = setOf(List(1 -> 5, 2 -> 2, 1 -> 2))
    val associative =
      eq(circ(circ(r1,r2), r3), circ(r1, circ(r2, r3)))
    associative
  }.holds

}
