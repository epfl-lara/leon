import leon.lang._
import leon.collection._

object FunctionCaching {

  case class Cache() {
    var cached: Map[BigInt, BigInt] = Map()
    //contains the set of elements where cache has been used
    var cacheHit: Set[BigInt] = Set()
  }

  def cachedFun(f: (BigInt) => BigInt, x: BigInt)(implicit cache: Cache) = {
    cache.cached.get(x) match {
      case None() =>
        val res = f(x)
        cache.cached = cache.cached.updated(x, res)
        res
      case Some(cached) =>
        cache.cacheHit = cache.cacheHit ++ Set(x)
        cached
    }
  }

  def funProperlyCached(x: BigInt, fun: (BigInt) => BigInt, trash: List[BigInt]): Boolean = {
    implicit val cache = Cache()
    val res1 = cachedFun(fun, x)
    multipleCalls(trash, x, fun)
    val res2 = cachedFun(fun, x)
    res1 == res2 && cache.cacheHit.contains(x)
  } holds

  def multipleCalls(args: List[BigInt], x: BigInt, fun: (BigInt) => BigInt)(implicit cache: Cache): Unit = {
    require(cache.cached.isDefinedAt(x))
    args match {
      case Nil() => ()
      case y::ys =>
        cachedFun(fun, y)
        multipleCalls(ys, x, fun)
    }
  } ensuring(_ => old(cache).cached.get(x) == cache.cached.get(x))

}
