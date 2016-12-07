import leon.lang._

object ArrayCopy {

  def copy(source: Array[Int], dest: Array[Int]): Unit = {
    require(source.length > 0 && source.length <= dest.length)
    val sourceLength = source.length

    var i = 0
    (while (i < source.length) {
      dest(i) = source(i)
      i = i + 1
    }) invariant {
      i >= 0 && i <= source.length &&
      (i == 0 || same(source, dest, 0, i)) &&
      source.length <= dest.length &&
      source.length == sourceLength 
    }

  } ensuring { _ => {
    source.length == old(source).length &&
    same(source, old(source), 0, source.length) && 
    source.length <= dest.length &&
    same(source, dest, 0, source.length)
  }}

  def same(a1: Array[Int], a2: Array[Int], from: Int, to: Int): Boolean = {
    require(from >= 0 && from <= a1.length && from <= a2.length && 
            to >= from && to <= a1.length && to <= a2.length)

    if(from == to || from == to) true
    else a1(from) == a2(from) && same(a1, a2, from+1, to)
  }


}
