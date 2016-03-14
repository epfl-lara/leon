import leon.lang._
import leon.collection._

object FunctionCaching {

  case class CachedFun[A,B](fun: (A) => B, var cached: Map[A, B], var cacheHit: Set[A]) {

    def call(a: A): B = {
      cached.get(a) match {
        case None() =>
          val res = fun(a)
          cached = cached.updated(a, res)
          res
        case Some(res) =>
          cacheHit = cacheHit ++ Set(a)
          res
      }
    }

  }

  def funProperlyCached(x: BigInt, fun: (BigInt) => BigInt, trash: List[BigInt]): Boolean = {
    val cachedFun = CachedFun[BigInt, BigInt](fun, Map(), Set())
    val res1 = cachedFun.call(x)
    multipleCalls(trash, cachedFun, x)
    val res2 = cachedFun.call(x)
    res1 == res2 && cachedFun.cacheHit.contains(x)
  } holds

  def multipleCalls(args: List[BigInt], cachedFun: CachedFun[BigInt, BigInt], x: BigInt): Unit = {
    require(cachedFun.cached.isDefinedAt(x))
    args match {
      case Nil() => ()
      case y::ys =>
        cachedFun.call(x)
        multipleCalls(ys, cachedFun, x)
    }
  } ensuring(_ => old(cachedFun).cached.get(x) == cachedFun.cached.get(x))

}
