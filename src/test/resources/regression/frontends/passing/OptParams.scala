/* Copyright 2009-2016 EPFL, Lausanne */

object OptParams {

  def foo( x : Int, y : Int = 12 ) = x + y

  def bar = foo(42)
  def baz = foo(1,2)



  abstract class Opt  {
    def opt( o : Opt = OptChild(), i : Int = 0) : Int = i + 1 
    def opt2 = opt()
  }
  case class OptChild() extends Opt
}
