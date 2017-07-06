import leon.lang._
import leon.collection._
import compiler.Trees._
import compiler.Desugar._

// Canary file for statistics extractor which lists the types in which we are interested

object Canary {
  def dummy[A]: A = error[A]("no impl.")

  def canary_Expr: Expr = dummy
  def canary_SimpleE: SimpleE = dummy

  def canary_Gen[T1]: T1 = dummy

  def canary_Unit: Unit = dummy
  def canary_Char: Char = dummy
  def canary_Int: Int = dummy
  def canary_BigInt: BigInt = dummy
  def canary_Boolean: Boolean = dummy
  def canary_Real: Real = dummy

  def canary_T1_List[T1]: List[T1] = dummy
  def canary_Char_List: List[Char] = dummy
  def canary_Int_List: List[Int] = dummy
  def canary_BigInt_List: List[BigInt] = dummy
  def canary_Boolean_List: List[Boolean] = dummy
  def canary_Real_List: List[Real] = dummy

  def canary_T1_Set[T1]: Set[T1] = dummy
  def canary_Char_Set: Set[Char] = dummy
  def canary_Int_Set: Set[Int] = dummy
  def canary_BigInt_Set: Set[BigInt] = dummy
  def canary_Boolean_Set: Set[Boolean] = dummy
  def canary_Real_Set: Set[Real] = dummy

  def canary_T1_Option[T1]: Option[T1] = dummy
  def canary_Char_Option: Option[Char] = dummy
  def canary_Int_Option: Option[Int] = dummy
  def canary_BigInt_Option: Option[BigInt] = dummy
  def canary_Boolean_Option: Option[Boolean] = dummy
  def canary_Real_Option: Option[Real] = dummy

}
