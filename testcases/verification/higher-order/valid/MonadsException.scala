import leon.lang._

object TryMonad {
  
  // Exception monad similar to Option monad, with a message for None
  
  sealed abstract class M[T] {
    def bind[S](f: T => M[S]): M[S] = {
      this match {
        case Exc(str) => Exc[S](str)
        case Success(t) => f(t)
      }
    }
  }
  case class Exc[T](err: BigInt) extends M[T]
  case class Success[T](t: T) extends M[T]

  // unit is success
  def unit[T](t:T) = Success(t)
  
  // all laws hold 
  def leftIdentity[T,S](t: T, f: T => M[S]): Boolean = {
    unit(t).bind(f) == f(t)
  }.holds
  
  def rightIdentity[T](m: M[T]): Boolean = {
    m.bind(unit(_)) == m
  }.holds

  def associativity[T,S,R](m: M[T], f: T => M[S], g: S => M[R]): Boolean = {
    m.bind(f).bind(g) == m.bind((t:T) => f(t).bind(g))
  }.holds
  
  // here is how we can use it
  
  def plus(x: M[BigInt], y: M[BigInt]) = {
    x.bind(xv => y.bind(yv => unit(xv+yv)))
  }
  
  def minus(x: M[BigInt], y: M[BigInt]) = {
    x.bind(xv => y.bind(yv => unit(xv - yv)))
  }
  
  def mul(x: M[BigInt], y: M[BigInt]): M[BigInt] = {
    x.bind(xv => 
      if (xv==0) x
      else y.bind(yv => unit(xv * yv)))
  }
  
  def mydiv(x: M[BigInt], y: M[BigInt]) = {
    x.bind(xv => y.bind(yv => 
      if (yv==0) Exc[BigInt](1001)
      else unit(xv/yv)))
  }
  
  
  def test1 = plus(unit(10), unit(32))
  def test2 = plus(mydiv(unit(10), unit(0)), unit(32))
  def test3 = plus(unit(3), plus(mydiv(unit(10), minus(unit(7), unit(7))), unit(32)))
  def test4 = mul(unit(0), test3)
}
