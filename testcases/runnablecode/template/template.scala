// Instrumented code here

// Instrumented code ends

  def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    def timed[T](code: => T)(cont: Long => Unit): T = {
      var t1 = System.nanoTime()
      val r = code
      cont((System.nanoTime() - t1))
      r
    }

    val points = (10 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
    val size = /* Size can be evaluated as a function of point or can also be done on the fly below*/
    var operTime = List[Any]() // Keeps track of operation count of the function
    var realTime = List[Any]() // Keeps track of the wall clock time

    points.foreach { i =>
      val input = {
        (1 to i).foldLeft[/*type*/](/*base*/) { (f, n) =>
          /*generate, for best results use worst case input*/
        }
      }
      operTime :+= (timed{ /*functionCall(Input)*/ }{realTime :+= _})._/*accessor*/
    }

    val orbTime = size.map(/*formula that Orb resulted in*/).toList // Keeps track of Orb predicted results

    /* Use a plotting library that will plot
    1) size -> orbTime
    2) size -> operTime
    3) size -> realTime
     */
  }
} // extra brace, just ensure `main` is inside the `object` of the benchmark