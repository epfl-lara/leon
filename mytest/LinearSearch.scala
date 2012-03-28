import leon.Utils._

object LinearSearch {

  def linearSearch(a: Map[Int, Int], size: Int, c: Int, j: Int): Boolean = ({
    require(size > 0 && j >= 0 && j < size)
    var i = 0
    var found = false
    (while(i < size) {
      if(a(i) == c)
        found = true
      i = i + 1
    }) invariant((if(j < i && !found) a(j) != c else true))
    found
  }) ensuring(res => (if(!res) a(j) != c else true))

}
