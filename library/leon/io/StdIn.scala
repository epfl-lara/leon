/* Copyright 2009-2016 EPFL, Lausanne */

package leon.io

import leon.annotation._

/*
 * NOTEs for GenC:
 * --------------
 *
 *  - `State` should be completely ignored as it is an artefact for verification
 *    proofs. TODO It might be interesting to completely drop it from the C code
 *    instead of aliasing it to void* and the null pointer.
 *
 *  - While `bool` is a standard C99 type (aliased to `_Bool`), there is no specifier
 *    for scan operation. Additionnally, the actual size of a boolean is platform
 *    dependent. Therefore, for simplicity, `readBoolean` is currently dropped.
 *
 *  - Currently, GenC doesn't support `BigInt` which implies that `readBigInt` is
 *    dropped as well.
 *
 */

object StdIn {

  @library
  @cCode.typedef(alias = "void*")
  case class State(var seed: BigInt)

  @library
  @cCode.function(code = "void* __FUNCTION__(void) { return NULL; }")
  def newState: State = State(0)

  @library
  @cCode.function(code = """
    |int32_t __FUNCTION__(void* unused) {
    |  int32_t x;
    |  scanf("%"SCNd32, &x);
    |  return x;
    |}
    """
  )
  def readInt(implicit state: State): Int = {
    state.seed += 1
    nativeReadInt(state.seed)
  }

  @library
  @extern
  @cCode.drop
  private def nativeReadInt(seed: BigInt): Int = {
    scala.io.StdIn.readInt
  } ensuring((x: Int) => true)

  @library
  @cCode.drop
  def readBigInt(implicit state: State): BigInt = {
    state.seed += 1
    nativeReadBigInt(state.seed)
  }

  @library
  @extern
  @cCode.drop
  private def nativeReadBigInt(seed: BigInt): BigInt = {
    BigInt(scala.io.StdIn.readInt)
  } ensuring((x: BigInt) => true)

  @library
  @cCode.drop
  def readBoolean(implicit state: State): Boolean = {
    state.seed += 1
    nativeReadBoolean(state.seed)
  }

  @library
  @extern
  @cCode.drop
  private def nativeReadBoolean(seed: BigInt): Boolean = {
    scala.io.StdIn.readBoolean
  } ensuring((x: Boolean) => true)

}
