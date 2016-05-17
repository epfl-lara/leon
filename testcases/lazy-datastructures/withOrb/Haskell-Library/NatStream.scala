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

object NatStream {

  /**
   * Stream for all natural numbers starting from n
   */
  val nats = SCons(0, Susp(() => genNextNatFrom(0)))
  @invisibleBody
  def genNextNatFrom(n: BigInt): LList = {
    require(n >= 0)
    val nn = n + 1
    SCons(n + 1, Susp(() => genNextNatFrom(nn)))
  } ensuring(_ => time <= ?) // Orb result: ??

  def nthElemInNats(n: BigInt) = {
    require(n >= 0)
    getnthElem(n, nats)
  } ensuring(_ => time <= ? * n + ?) // Orb result: ??

}
