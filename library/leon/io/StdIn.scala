/* Copyright 2009-2016 EPFL, Lausanne */

package leon.io

import leon.annotation._

object StdIn {

  @library
  case class State(var seed: BigInt)

  @library
  def newState: State = State(0)

  @library
  @isabelle.noBody()
  def readInt(implicit state: State): Int = {
    state.seed += 1
    nativeReadInt(state.seed)
  }

  @library
  @extern
  @isabelle.noBody()
  private def nativeReadInt(implicit state: State)(seed: BigInt): Int = {
    scala.io.StdIn.readInt
  } ensuring((x: Int) => true)

  @library
  @isabelle.noBody()
  def readBigInt(implicit state: State): BigInt = {
    state.seed += 1
    nativeReadBigInt(state.seed)
  }

  @library
  @extern
  @isabelle.noBody()
  private def nativeReadBigInt(seed: BigInt): BigInt = {
    BigInt(scala.io.StdIn.readInt)
  } ensuring((x: BigInt) => true)

  @library
  @isabelle.noBody()
  def readBoolean(implicit state: State): Boolean = {
    state.seed += 1
    nativeReadBoolean(state.seed)
  }

  @library
  @extern
  @isabelle.noBody()
  private def nativeReadBoolean(seed: BigInt): Boolean = {
    scala.io.StdIn.readBoolean
  } ensuring((x: Boolean) => true)

}
