import leon.Utils._

/* The calculus of Computation textbook */

object LinearSearch {

  def linearSearch(a: Map[Int, Int], size: Int, c: Int): Boolean = ({
    require(size <= 5 && isArray(a, size))
    var i = 0
    var found = false
    (while(i < size) {
      if(a(i) == c)
        found = true
      i = i + 1
    }) invariant(i <= size && 
                 i >= 0 && 
                 (if(found) contains(a, i, c) else !contains(a, i, c))
                )
    found
  }) ensuring(res => if(res) contains(a, size, c) else !contains(a, size, c))

  def contains(a: Map[Int, Int], size: Int, c: Int): Boolean = {
    require(isArray(a, size) && size <= 5)
    content(a, size).contains(c)
  }
  

  def content(a: Map[Int, Int], size: Int): Set[Int] = {
    require(isArray(a, size) && size <= 5)
    var set = Set.empty[Int]
    var i = 0
    (while(i < size) {
      set = set ++ Set(a(i))
      i = i + 1
    }) invariant(i >= 0 && i <= size)
    set
  }

  def isArray(a: Map[Int, Int], size: Int): Boolean = {

    def rec(i: Int): Boolean = {
      require(i >= 0)  
      if(i >= size) true else {
        if(a.isDefinedAt(i)) rec(i+1) else false
      }
    }

    if(size < 0)
      false
    else
      rec(0)
  }
}
