import leon.lang._
import leon.collection._
import leon.lang.synthesis._

object Holes {
  def abs1(a: Int) = {
    if (?(true, false)) {
      a
    } else {
      -a
    }
  } ensuring {
    _ >= 0
  }

  def abs2(a: Int) = {
    if (???[Boolean]) {
      a
    } else {
      -a
    }
  } ensuring {
    _ >= 0
  }

  def abs3(a: Int) = {
    if (?(a > 0, a < 0)) {
      a
    } else {
      -a
    }
  } ensuring {
    _ >= 0
  }
}
