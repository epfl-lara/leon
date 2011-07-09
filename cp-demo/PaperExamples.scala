import cp.Definitions._
import cp.Terms._

object PaperExamples extends App {
  def p(str : String, a : =>Any) : Unit = {
    println(str + " : " + a.toString)
  }

  val c1 : Constraint2[Int,Int] = ((x : Int, y : Int) => 2 * x + 3 * y == 10 && x >= 0 && y >= 0)
  p("c1(2,1)", c1(2,1))
  p("c1(5,0)", c1(5,0))
  p("c1.solve", c1.solve)
  p("c1.findAll.toList", c1.findAll.toList)

  def bounded(m : Int) : Constraint1[Int] = ((x : Int) => x >= 0 && x <= m)
  p("bounded(3).findAll.toList", bounded(3).findAll.toList)

  def boundedPair(m : Int) : Constraint2[Int,Int] = {
    val b = bounded(m)
    //b product b
    ((x : Int, y : Int) => x >= 0 && x <= m && y >= 0 && y <= m)
  }

  def boundedQ(m : Int) : Constraint4[Int,Int,Int,Int] = {
    ((x : Int, y : Int, z : Int, u : Int) =>
      x >= 0 && x <= m &&
      y >= 0 && y <= m &&
      z >= 0 && z <= m &&
      u >= 0 && u <= m)
  }

  @spec def det(a : Int, b : Int, c : Int, d : Int) : Int = a*d - b*c
  @spec def isUnimodular(a : Int, b : Int, c : Int, d : Int) : Boolean = {
    val dt = det(a,b,c,d)
    dt == 1 || dt == -1
  }

  def inverse(a : Int, b : Int, c : Int, d : Int) : Option[(Int,Int,Int,Int)] = 
    ((x: Int, y: Int, z: Int, u: Int) =>
      a*x+b*z == 1 && 
      a*y+b*u == 0 &&
      c*x+d*z == 0 &&
      c*y+d*u == 1).find

  def boundedUnimodular(m : Int) = {
    boundedQ(m) &&
    ((a : Int, b : Int, c : Int, d : Int) => isUnimodular(a,b,c,d)) // TODO would be great if we could write this as isUnimodular _ :)
  }
  p("Unimodular count", (0 to 5).map(boundedUnimodular(_).findAll.size).toList)

  p("inverse of(4,5,3,4): ", inverse(4,5,3,4))
  p("inverse of(4,5,3,0): ", inverse(4,5,3,0))
}
