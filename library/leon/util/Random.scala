/* Copyright 2009-2016 EPFL, Lausanne */

package leon.util

import leon.annotation._
import leon.lang.xlang._

object Random {

  @library
  case class State(var seed: BigInt)

  @library
  def newState: State = State(0)


  @library
  @isabelle.noBody()
  def nextBoolean(implicit state: State): Boolean = {
    state.seed += 1
    nativeNextBoolean
  } ensuring((x: Boolean) => true)

  @library
  @extern
  @isabelle.noBody()
  private def nativeNextBoolean(implicit state: State): Boolean = {
    scala.util.Random.nextBoolean
  } ensuring((x: Boolean) => true)



  @library
  @isabelle.noBody()
  def nextInt(implicit state: State): Int = {
    state.seed += 1
    nativeNextInt
  } ensuring((x: Int) => true)

  @library
  @extern
  @isabelle.noBody()
  private def nativeNextInt(implicit state: State): Int = {
    scala.util.Random.nextInt
  } ensuring((x: Int) => true)



  @library
  @isabelle.noBody()
  def nextInt(max: Int)(implicit state: State): Int = {
    require(max > 0)
    state.seed += 1
    nativeNextInt(max)
  } ensuring(res => res >= 0 && res < max)

  @library
  @extern
  @isabelle.noBody()
  def nativeNextInt(max: Int)(implicit state: State): Int = {
    scala.util.Random.nextInt(max)
  } ensuring(res => res >= 0 && res < max)



  @library
  @isabelle.noBody()
  def nextBigInt(implicit state: State): BigInt = {
    state.seed += 1
    nativeNextBigInt
  } ensuring((x: BigInt) => true)

  @library
  @extern
  @isabelle.noBody()
  private def nativeNextBigInt(implicit state: State): BigInt = {
    BigInt(scala.util.Random.nextInt)
  } ensuring((x: BigInt) => true)



  @library
  @isabelle.noBody()
  def nextBigInt(max: BigInt)(implicit state: State): BigInt = {
    require(max > 0)
    state.seed += 1
    nativeNextBigInt(max)
  } ensuring((res: BigInt) => res >= 0 && res < max)

  @library
  @extern
  @isabelle.noBody()
  private def nativeNextBigInt(max: BigInt)(implicit state: State): BigInt = {
    BigInt(scala.util.Random.nextInt(max.toInt))
  } ensuring((x: BigInt) => x >= 0 && x < max)

}
