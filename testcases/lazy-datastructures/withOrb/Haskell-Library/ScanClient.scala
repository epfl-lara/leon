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

object ScanClient {

  @ignore
  val array = Array[BigInt]()
  @extern
  def f(n: BigInt, m: BigInt): BigInt = {
    array(0)
  } ensuring(_ => time <= 1)

  def nthElemAfterScan(n: BigInt, z: BigInt) = {
    require(n >= 0)
    getnthElem(n, scan(f, z, natsFromn(0)))
  } ensuring(_ => time <= ? * n + ?) // Orb result: ??

}
