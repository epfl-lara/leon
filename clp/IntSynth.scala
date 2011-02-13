import scala.collection.immutable.Set
import funcheck.Annotations._
import funcheck.Utils._

object IntSynth {

  // What could this be?

  def specT(time : Int, h : Int, m : Int, s : Int) : Boolean = {
    require(0 <= time)
    time == 3600 * h + 60 * m + s &&
    0 <= h && 
    0 <= m && m < 60 &&
    0 <= s && s < 60
  }
  def f200(h : Int, m : Int, s : Int) : Boolean = {
    !specT(10000, h, m, s)
  } holds

  // Square root

  def specSqr(x : Int, y : Int) : Boolean = {
    require (0 <= y)
    x*x <= y && (x+1)*(x+1) > y
  }
  def sqrt100(x : Int) : Boolean = {
    !specSqr(x, 1000)
  } holds

  // Sketching

  def mySquare(x : Int, q1 : Int, q2 : Int, q3 : Int) : Int = {
    require (x >= 0)
    if (x <= 1) x + q1
    else q2*x + mySquare(x - 2, q1,q2,q3) + q3
  }

  def shouldSquare(q1 : Int, q2 : Int, q3 : Int) : Boolean = {
    !(mySquare(3,q1,q2,q3)==9 &&
      mySquare(4,q1,q2,q3)==16 &&
      mySquare(5,q1,q2,q3)==25)
  } holds

  //def gotThis(x : Int) = mySquare(x, 0, 4, -4)
  //println(gotThis(10)) --> 100
}
