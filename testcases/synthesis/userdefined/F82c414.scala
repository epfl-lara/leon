import leon.annotation._
import leon.collection._
import leon.grammar._
import leon.lang._
import leon.proof._

// Canary file for statistics extractor which lists the types in which we are interested

object F82c414 {
  // Full grammar
  def canary[T1, T2](t1: T1, t2: T2): T1 = {
    variable[T1]

    val f82c414_Unit: Unit = ()
    val f82c414_Char: Char = 'a'
    val f82c414_Int: Int = 0
    val f82c414_BigInt: BigInt = BigInt(0)
    val f82c414_Boolean: Boolean = true
    val f82c414_Real: Real = Real(0)
    val canary1 = (f82c414_Unit, f82c414_Char, f82c414_Int, f82c414_BigInt, f82c414_Boolean, f82c414_Real)

    def cons[T](t: T, l: List[T]): List[T] = Cons(t, l)
    val f82c414_T1_List: List[T1] = cons(t1, Nil())
    val f82c414_Char_List: List[Char] = cons(f82c414_Char, Nil())
    val f82c414_Int_List: List[Int] = cons(f82c414_Int, Nil())
    val f82c414_BigInt_List: List[BigInt] = cons(f82c414_BigInt, Nil())
    val f82c414_Boolean_List: List[Boolean] = cons(f82c414_Boolean, Nil())
    val f82c414_Real_List: List[Real] = cons(f82c414_Real, Nil())
    val canary2 = (f82c414_T1_List, f82c414_Char_List, f82c414_Int_List, f82c414_BigInt_List, f82c414_Boolean_List, f82c414_Real_List)

    val f82c414_T1_Set: Set[T1] = Set(t1)
    val f82c414_Char_Set: Set[Char] = Set(f82c414_Char)
    val f82c414_Int_Set: Set[Int] = Set(f82c414_Int)
    val f82c414_BigInt_Set: Set[BigInt] = Set(f82c414_BigInt)
    val f82c414_Boolean_Set: Set[Boolean] = Set(f82c414_Boolean)
    val f82c414_Real_Set: Set[Real] = Set(f82c414_Real)
    val canary3 = (f82c414_T1_Set, f82c414_Char_Set, f82c414_Int_Set, f82c414_BigInt_Set, f82c414_Boolean_Set, f82c414_Real_Set)

    val f82c414_T1_Option: Option[T1] = Some(t1)
    val f82c414_Char_Option: Option[Char] = Some(f82c414_Char)
    val f82c414_Int_Option: Option[Int] = Some(f82c414_Int)
    val f82c414_BigInt_Option: Option[BigInt] = Some(f82c414_BigInt)
    val f82c414_Boolean_Option: Option[Boolean] = Some(f82c414_Boolean)
    val f82c414_Real_Option: Option[Real] = Some(f82c414_Real)
    val canary4 = (f82c414_T1_Option, f82c414_Char_Option, f82c414_Int_Option, f82c414_BigInt_Option, f82c414_Boolean_Option, f82c414_Real_Option)

    t1
  }
  /*
  // BigInt, Boolean, List
  def canary[T1, T2](t1: T1, t2: T2): T1 = {
    variable[T1]

    val f82c414_BigInt: BigInt = BigInt(0)
    val f82c414_Boolean: Boolean = true
    val canary1 = (f82c414_BigInt, f82c414_Boolean)

    t1
  }*/

}
