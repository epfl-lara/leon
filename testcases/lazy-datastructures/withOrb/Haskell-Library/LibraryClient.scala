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

  def nthElemInNatsFromM(n: BigInt, M: BigInt) = {
    require(n >= 0)
    getnthElem(n, natsFromn(M))
  } ensuring(_ => time <= ? * n + ?) // Orb result: ??

   def nthElemInRepeat(n: BigInt, m: BigInt) = {
    require(n >= 0)
    getnthElem(n, repeat(m))
  } ensuring (_ => time <= ? * n + ?) // Orb result: ??

  def nthElemInCycle(n: BigInt, l: List[BigInt]) = {
    require(n >= 0)
    getnthElem(n, cycle(l))
  } ensuring (_ => time <= ? * n + ?) // Orb result: ??

  @ignore
  val array = Array[BigInt]()
  @extern
  def f(n: BigInt): BigInt = {
    array(0)
  } ensuring (_ => time <= 1)

  def nthElemAfterMap(n: BigInt) = {
    require(n >= 0)
    getnthElem(n, map(f, natsFromn(0)))
  } ensuring (_ => time <= ? * n + ?) // Orb result: ??

  @extern
  def p(n: BigInt): Boolean = {
    array(0) == 0
  } ensuring (_ => time <= 1)

  def nthElemAfterTakeWhile(n: BigInt) = {
    require(n >= 0)
    getnthElem(n, takeWhile(p, natsFromn(0)))
  } ensuring (_ => time <= ? * n + ?) // Orb result: ??

  @extern
  def acc(n: BigInt, m: BigInt): BigInt = {
    array(0)
  } ensuring(_ => time <= 1)

  def nthElemAfterScan(n: BigInt, z: BigInt) = {
    require(n >= 0)
    getnthElem(n, scan(acc, z, natsFromn(0)))
  } ensuring(_ => time <= ? * n + ?) // Orb result: ??

  @extern
  def tupFunc(n: BigInt): (BigInt, BigInt) = {
    (array(0), array(0))
  } ensuring(_ => time <= 1)

  def nthElemAfterUnfold(n: BigInt, c: BigInt) = {
    require(n >= 0)
    getnthElem(n, unfold(tupFunc, c))
  } ensuring(_ => time <= ? * n + ?) // Orb result: ??

}
