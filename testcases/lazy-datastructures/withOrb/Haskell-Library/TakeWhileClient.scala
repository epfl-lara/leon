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

object TakeWhileClient {

  @ignore
  val array = Array[Boolean]()
  @extern
  def p(n: BigInt): Boolean = {
    array(0)
  } ensuring(_ => time <= 1)

  // def takeWhileList(p: BigInt => Boolean) = {
  //   takeWhile(p, natsFromn(0))
  // } ensuring(res => time <= ? * res.size + ?) // Orb result: ??

}
