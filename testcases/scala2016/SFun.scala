import leon.lang._
import leon.annotation._
import leon.collection._

object SFuns {

  case class State[A](var x: A)

  case class SFun[A, S, B](state: State[S], f: (A, State[S]) => B) {
    def apply(x: A): B = f(x, state)
  }


  def counter(init: BigInt): SFun[BigInt, BigInt, BigInt] = {
    val closure = SFun(State(init), (n: BigInt, s: State[BigInt]) => {
      s.x += 1
      (s.x - 1)
    })
    closure
  }


  def test(init: BigInt): Unit = {
    val gen = counter(init)
    val x1 = gen(0)
    assert(x1 == init)
    val x2 = gen(0)
    assert(x2 == init+1)
    val x3 = gen(0)
    assert(x3 == init+2)
  }


  def window2(init: (BigInt, BigInt)): SFun[BigInt, (BigInt, BigInt), BigInt] = {

    //state is used to remember last 2 numbers seen, and return sum of last 3
    val closure = (n: BigInt, s: State[(BigInt, BigInt)]) => {
      val res = n + s.x._1 + s.x._2
      s.x = (n, s.x._1)
      res
    }
    
    SFun(State(init), closure)
  }

  def testWindow2(): Unit = {
    val gen = window2((0, 0))
    val x1 = gen(1)
    assert(x1 == 1)
    val x2 = gen(1)
    assert(x2 == 2)
    val x3 = gen(2)
    assert(x3 == 4)
    val x4 = gen(2)
    assert(x4 == 5)
  }


  def foreach[A, S](l: List[A], sf: SFun[A, S, Unit]): Unit = l match {
    case x::xs => 
      sf(x)
      foreach(xs, sf)
    case Nil() => ()
  }

  def testForeach(): Unit = {
    val l = List[BigInt](1,2,3,4,5)
    val closure = SFun(State[BigInt](0), (n: BigInt, s: State[BigInt]) => { s.x += n })
    foreach(l, closure)
    assert(closure.state.x == 15)
  }


  def makeCounter: SFun[Unit, BigInt, BigInt] = {
    SFun(State(0), 
         (_: Unit, s: State[BigInt]) => { s.x += 1; s.x })
  }
  def testCounter(): Unit = {
    val counter = makeCounter
    val x1 = counter(())
    assert(x1 == 1)
    val x2 = counter(())
    assert(x2 == 2)
  }


}
