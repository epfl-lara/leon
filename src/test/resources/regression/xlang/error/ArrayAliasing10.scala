/* Copyright 2009-2015 EPFL, Lausanne */

object ArrayAliasing10 {

  def foo(): Int = {
    val a = Array.fill(5)(0)

    def rec(): Array[Int] = {
      
      def nestedRec(): Array[Int] = {
        a
      }
      nestedRec()
    }
    val b = rec()
    b(0)
  }

}
