import leon.lang._

object Fib {


  case class World(var count: BigInt, var cached: Map[BigInt, BigInt])

  def fib(x: BigInt)(implicit world: World): BigInt = {
    require(x > 0)
    world.count += 1
    if(x == 1 || x == 2) {
      world.cached += (x -> 1)
      1
    } else {
      val x1 = world.cached.get(x-1) match {
        case None() => fib(x-1)
        case Some(res) => res
      }
      val x2 = world.cached.get(x-2) match {
        case None() => fib(x-2)
        case Some(res) => res
      }
      val res = x1+x2
      world.cached += (x -> res)
      res
    }
  }

  def main: Unit = {
    implicit val world = World(0, Map())
    val r1 = fib(5)
    val r2 = fib(7)
    assert(r1 == 5 && r2 == 13 && world.count == 7)
  }

}
