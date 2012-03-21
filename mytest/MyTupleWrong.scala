object MyTupleWrong {

  def foo(): Int = {
    val t = (1, true)
    val a1 = t._1
    val a2 = t._2
    val a3 = t._3
    a1
  }

}


// vim: set ts=4 sw=4 et:
