package leon.utils

class Bijection[A, B] {
  var a2b = Map[A, B]()
  var b2a = Map[B, A]()

  def +=(a: A, b: B): Unit = {
    a2b += a -> b
    b2a += b -> a
  }

  def +=(t: (A,B)): Unit = {
    this += (t._1, t._2)
  }

  def clear(): Unit = {
    a2b = Map()
    b2a = Map()
  }

  def getA(b: B) = b2a.get(b)
  def getB(a: A) = a2b.get(a)

  def toA(b: B) = getA(b).get
  def toB(a: A) = getB(a).get

  def fromA(a: A) = getB(a).get
  def fromB(b: B) = getA(b).get

  def cachedB(a: A)(c: => B) = {
    getB(a).getOrElse {
      val res = c
      this += a -> res
      res
    }
  }

  def cachedA(b: B)(c: => A) = {
    getA(b).getOrElse {
      val res = c
      this += res -> b
      res
    }
  }

  def containsA(a: A) = a2b contains a
  def containsB(b: B) = b2a contains b

  def aSet = a2b.keySet
  def bSet = b2a.keySet
}
