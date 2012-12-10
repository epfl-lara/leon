object Prog004 {
  def set1() : Set[Int] = {
    Set(6, 7)
  }

  def set2() : Set[Int] = {
    set1() ++ Set(4)
  }

  def set3() : Set[Int] = {
    set2() ** set1()
  }

  def set4() : Set[Int] = {
    set2() -- set1()
  }
}
