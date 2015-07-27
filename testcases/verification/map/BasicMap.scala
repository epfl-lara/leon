import scala.collection.immutable.Set
import leon.annotation._
import leon.lang._

object BasicMap {

  def insert(m: Map[BigInt, BigInt], key: BigInt, value: BigInt): Map[BigInt, BigInt] = {
    require(!m.isDefinedAt(key))
    m + (key -> value)
  } ensuring(res => res(key) == value)

  def unionWorks(m1: Map[BigInt, BigInt], m2: Map[BigInt, BigInt], key: BigInt): Boolean = {
    require(m1.isDefinedAt(key) || m2.isDefinedAt(key))
    (m1 ++ m2).isDefinedAt(key)
  }.holds
  
}
