object MyTuple1 {

  def foo(): Int = {
    val t = (1, true)
    val a1 = t._1
    val a2 = t._2
    a1
  } ensuring( _ > 0)

}

