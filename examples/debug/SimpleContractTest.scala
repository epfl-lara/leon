package debug

object SimpleContractTest {
  def main(args: Array[String]): Unit = {
    println("All set.")

    println(checkedFunction(12))

    // pre-cond fails
    //println(checkedFunction(-1))

    // post-cond fails
    //println(checkedFunction(1))

  }

  def checkedFunction(i: Int): Int = { require(i >= 0) 
    i * i
  } ensuring(res => (res > i  && res >= 0))
}
