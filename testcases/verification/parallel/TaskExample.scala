
import leon._
import leon.lang._
import leon.annotation._
import leon.collection._
import leon.par.Tasks._

object TaskExample {

  def sumList(xs: List[Int]): Int = {
    xs match {
      case Nil() => 0
      case Cons(x, xs1) => x + sumList(xs1)
    }
  }
  
  def sumPar1(l1: List[Int], l2: List[Int]) : Int = {
    val (s1,s2) = parallel(sumList(l1), sumList(l2))
    s1 + s2
  }

  def sumPar2(l1: List[Int], l2: List[Int]) : Int = {
    val s1 = task { sumList(l1) }
    val s2 = sumList(l2)
    s1.join + s2
  }

  def test1 : Boolean = {
    val l1 = List(1, 2, 3, 4, 5)
    val l2 = List(10, 20, 30, 40, 50)
    val a1 = sumPar1(l1, l2)
    val a2 = sumPar2(l1, l2)
    a1 == a2
  }.holds

  def test(l1: List[Int], l2: List[Int]) : Boolean = {
    val a1 = sumPar1(l1, l2)
    val a2 = sumPar2(l1, l2)
    a1 == a2
  }.holds

}
