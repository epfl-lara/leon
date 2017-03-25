/* Copyright 2009-2016 EPFL, Lausanne */

package leon.io

import leon.annotation._
import scala.math.BigInt

@library
@cCode.typedef(alias = "void*")
case class State(var seed: BigInt)