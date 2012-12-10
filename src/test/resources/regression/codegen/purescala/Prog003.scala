object Prog003 {
  // Some tests for tuples
  def wrap(x : Int, b : Boolean) : (Int,Boolean) = (x,b)

  def fst(t : (Int,Boolean)) : Int = t._1

  def snd(t : (Int,Boolean)) : Boolean = t._2

  def swap(t : (Int,Boolean)) : (Boolean,Int) = {
    val (i,b) = t

    (b,i)
  }
}
