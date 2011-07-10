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

  def satSolve(problem : Seq[Seq[Int]]) = {
    problem.map(l => l.map(i => {
      val id = scala.math.abs(i)
      val isPos = i > 0
      ((m : Map[Int,Boolean]) => m(id) == isPos).c
    }).reduceLeft(_ || _)).reduceLeft(_ && _).find
  }

  println("satSolve(something sat)", satSolve(List(List(-1, 2, 3), List(1, -2, 4), List(-3, -4))))
  println("satSolve(something unsat)", satSolve(List(List(1, 2), List(1, -2), List(-1, 2), List(-1, -2))))


  @spec object SendMoreMoney {
    sealed abstract class Letter
    case class D() extends Letter
    case class E() extends Letter
    case class M() extends Letter
    case class N() extends Letter
    case class O() extends Letter
    case class R() extends Letter
    case class S() extends Letter
    case class Y() extends Letter
    val letters : List[Letter] = List(D(), E(), M(), N(), O(), R(), S(), Y())

    def run : Unit = {
      val m = ((m : Map[Letter,Int]) => true).lazySolve
      for(l <- letters) {
        assuming(m(l) >= 0 && m(l) <= 9) {
          println("OK for " + l)
        }

      }
      // simpler, crashes too:
      //assuming(m(S()) >= 0 && m(S()) <= 9) {
      //  println("OK for " + S())
      //}

      //println("A solution : " + m.value)

      // functional-style, crashed because of if
//      for(m <- ((m: Map[Letter,Int]) => 
//        1000 * m(S()) + 100 * m(E()) + 10 * m(N()) + m(D()) +
//        1000 * m(M()) + 100 * m(O()) + 10 * m(R()) + m(E()) ==
//        10000 * m(M()) + 1000 * m(O()) + 100 * m(N()) + 10 * m(E()) + m(Y())).c.lazyFindAll if(
//          m(S()) >= 0 && m(S()) <= 9)
//        ){
//        println(m)
//      }
    }
  }

  SendMoreMoney.run
}
