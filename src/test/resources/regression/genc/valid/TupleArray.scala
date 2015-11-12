import leon.lang._

object TupleArray {
  def exists(av: (Array[Int], Int)): Boolean = {
    var i = 0;
    var found = false;
    while (!found && i < av._1.length) {
      found = av._1(i) == av._2
      i = i + 1
    }
    found
  }

  def main = {
    val a = Array(0, 1, 5, -5, 9)
    val e1 = exists((a, 0))
    val e2 = exists((a, -1))
    if (e1 && !e2) 0
    else -1
  }

}
