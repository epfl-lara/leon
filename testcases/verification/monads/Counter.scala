/* Copyright 2009-2015 EPFL, Lausanne */

import leon.monads.state._

object Counter {

  import State._

  def counter(init: BigInt) = {

    @inline
    def tick = modify[BigInt](_ + 1)

    init >:: (for {
      _ <- tick
      _ <- tick
      _ <- tick
      r <- get
    } yield r)

  } ensuring( _ == init + 3 )
}