import funcheck.Utils._
import funcheck.Annotations._

import cp.Definitions._

@spec object AbstractMemory {
  // - our maps are already ``canonicalized''

  def init(): Map[Int,Int] = {
    Map.empty[Int,Int]
  }

  def write(memory: Map[Int,Int], address: Int, data: Int): Map[Int,Int] = {
    memory.updated(address, data)
  }

  def read(memory: Map[Int,Int], address: Int): Int = {
    require(memory.isDefinedAt(address))
    memory(address)
  }

  def writeRead(m: Map[Int,Int], a: Int, d: Int): Boolean = {
    (m.updated(a, d))(a) == d
  } holds

  def writeIdempotent(m: Map[Int,Int], a: Int, d: Int): Boolean = {
    val m2 = m.updated(a, d)
    val m3 = m2.updated(a, d)
    m2 == m3
  } holds
}
