import scala.collection.immutable.Set
import scala.collection.immutable.Map
import funcheck.Utils._
import funcheck.Annotations._

object Maps { 
  // To implement:
  //   - updated -> MapUnion (simply mkStore)
  //   - isDefinedAt -> MapIsDefinedAt (look it up by using mkSelect, check if it is MapSome(bla)
  //   - apply -> MapGet (look it up by using mkSelect, and return the value if it is MapSome(v)
  //
  //   - constant maps -> FiniteMap , empty map -> EmptyMap (use store on mkArrayConst with default value MapNone)

  // deal with it in:
  // - trees OK (we assume current structure is suitable)
  // - evaluator
  // - codeextraction OK
  // - extractors OK
  // - solver
  // - printer OK

  sealed abstract class List
  case class Cons(head : Int, tail : List) extends List
  case class Nil() extends List

  def applyTest(m : Map[Int,Int], i : Int) : Int = m(i)

  def isDefinedAtTest(m : Map[Int,Int], i : Int) : Boolean = m.isDefinedAt(i)

  def emptyTest() : Map[Int,Int] = Map.empty[Int,Int]

  def updatedTest(m : Map[Int,Int]) : Map[Int,Int] = m.updated(1, 2)

  def useCase(map : Map[Int,Int], k : Int, v : Int) : Boolean = {
    val map2 = map.updated(k, v)
    map2.isDefinedAt(k)
  } holds

  def useCase2(map : Map[Int,Int], k : Int, v : Int) : Map[Int,Int] = {
    val map2 = map.updated(k, v)
    map2
  } ensuring (res => res.isDefinedAt(k))

  def readOverWrite(m : Map[Int,Int], k1 : Int, k2 : Int, e : Int) : Boolean = {
    val newM = m.updated(k2, e)
    if (m.isDefinedAt(k1))
      newM(k1) == (if (k1 == k2) e else m(k1))
    else
      true
  } holds

  def findModel(m : Map[Int,List]) : Boolean = {
    m == Map.empty[Int,List].updated(42, Nil()) || m == Map.empty[Int, List]
  } holds
}
