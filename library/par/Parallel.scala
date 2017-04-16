package leon.par

import leon._
import leon.lang._
import leon.annotation._

@library
object Tasks {
  
  def parallel[A,B](x: => A, y: => B) : (A,B) = {
    (x,y)
  }

  case class Task[A](c: A) {
    def join: A = c
  }

  def task[A](c: A) = Task(c)

}
