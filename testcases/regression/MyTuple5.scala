object MyTuple4 {

  def foo(): Int = {
    val t = ((2, 3), true)
    t._1._2
  } ensuring( _ == 3)

}

// vim: set ts=4 sw=4 et:
