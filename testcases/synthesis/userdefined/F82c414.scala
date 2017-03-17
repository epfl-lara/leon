import leon.annotation._
import leon.collection._
import leon.lang._
import leon.proof._

// Canary file for statistics extractor which lists the types in which we are interested

object F82c414 {

  def canary[T1, T2](t1: T1, t2: T2): T1 = {
    val f82c414_0: Unit = ()

    val f82c414_1: Int = 0
    val f82c414_2: BigInt = BigInt(0)
    val f82c414_3: Boolean = true

    def cons[T](t: T, l: List[T]): List[T] = Cons(t, l)
    val f82c414_4: List[T1] = cons(t1, Nil())
    val f82c414_5: List[Int] = cons(f82c414_1, Nil())
    val f82c414_6: List[BigInt] = cons(f82c414_2, Nil())

    val f82c414_7: Set[T1] = Set(t1)
    val f82c414_8: Set[Int] = Set(f82c414_1)
    val f82c414_9: Set[BigInt] = Set(f82c414_2)

    val f82c414_10: Option[T1] = Some(t1)
    val f82c414_11: Option[Int] = Some(f82c414_1)
    val f82c414_12: Option[BigInt] = Some(f82c414_2)
    val f82c414_13: Option[Boolean] = Some(f82c414_3)

    // TODO! Also include pairs!

    val canary0 = f82c414_0
    val canary1 = (f82c414_1, f82c414_2, f82c414_3)
    val canary2 = (f82c414_4, f82c414_5, f82c414_6)
    val canary3 = (f82c414_7, f82c414_8, f82c414_9)
    val canary4 = (f82c414_10, f82c414_11, f82c414_12, f82c414_13)

    t1
  }

}
