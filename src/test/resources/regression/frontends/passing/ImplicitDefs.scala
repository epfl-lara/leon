/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import scala.language.implicitConversions

object Preamble {
  case class BoolOps(b: Boolean) {
    def <==>(o: Boolean) = {
      (!b || o) && (!o || b)
    }
  }

  implicit def bTobOps(b: Boolean): BoolOps = BoolOps(b)
  def bTobOps2(b: Boolean): BoolOps = BoolOps(b)
}

object Foo {
  import Preamble._

  def f(b: Boolean) = BoolOps(b)

  def test0(a: BigInt) = {
    f((a > 1)).<==>(a > 0)
  }.holds

  def test1(a: BigInt) = {
    bTobOps2(a > 1).<==>(a > 0)
  }.holds

  def test2(a: BigInt) = {
    bTobOps(a > 1).<==>(a > 0)
  }.holds
}
