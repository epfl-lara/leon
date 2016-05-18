package stream

import leon._
import lang._
import annotation._
import instrumentation._
import mem._
import higherorder._
import collection._
import invariant._
import StreamLibrary._

object CycleAndRepeatClient {

  def nthElemInRepeat(n: BigInt, m: BigInt) = {
    require(n >= 0)
    getnthElem(n, repeat(m))
  } ensuring (_ => time <= ? * n + ?) // Orb result: ??

  def nthElemInCycle(n: BigInt, l: List[BigInt]) = {
    require(n >= 0)
    getnthElem(n, cycle(l))
  } ensuring (_ => time <= ? * n + ?) // Orb result: ??
  
}
