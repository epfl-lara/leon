import cp.Definitions._
import cp.Terms._
import cp.LTrees._

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
      val c : Constraint1[Map[Int,Boolean]] = ((m : Map[Int,Boolean]) => m(id) == isPos)
      c
    }).reduceLeft(_ || _)).reduceLeft(_ && _).find
  }

  println("satSolve(p)", satSolve(Seq(Seq(1,-2,-3), Seq(2,3,4), Seq(-1,-4))))
  println("satSolve(Seq(Seq(1,2), Seq(-1), Seq(-2)))", satSolve(Seq(Seq(1,2), Seq(-1), Seq(-2))))
//  println("satSolve(something sat)", satSolve(List(List(-1, 2, 3), List(1, -2, 4), List(-3, -4))))
//  println("satSolve(something unsat)", satSolve(List(List(1, 2), List(1, -2), List(-1, 2), List(-1, -2))))

  @spec def divides(i : Int, j : Int) : Boolean = i * (j / i) == j
  @spec def noneDivides(from : Int, j : Int) : Boolean = {
    if(from == j) {
      true
    } else {
      !divides(from, j) && noneDivides(from+1, j)
    }
  }
  @spec def isPrime(i : Int) : Boolean = (i >= 2 && noneDivides(2, i))

  val primes = (isPrime(_:Int)) minimizing((x:Int) => x) findAll

  primes.take(25).foreach(println(_))

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
      val anyInt = ((n : Int) => true)

      val letters @ Seq(s,e,n,d,m,o,r,y) = Seq.fill(8)(anyInt.lazySolve)

      for(l <- letters) {
        when(l >= 0 && l <= 0) {
          ;
        } otherwise {
          println("Couldn't constrain letter.")
        }
      }

      //assuming(distinct(s,e,n,d,m,o,r,y)) {
      assuming(
                  s != e && s != n && s != d && s != m && s != o && s != r && s != y &&
        e != s &&           e != n && e != d && e != m && e != o && e != r && e != y &&
        n != s && n != e &&           n != d && n != m && n != o && n != r && n != y &&
        d != s && d != e && d != n &&           d != m && d != o && d != r && d != y &&
        m != s && m != e && m != n && m != d &&           m != o && m != r && m != y &&
        o != s && o != e && o != n && o != d && o != m &&           o != r && o != y &&
        r != s && r != e && r != n && r != d && r != m && r != o &&           r != y &&
        y != s && y != e && y != n && y != d && y != m && y != o && y != r             )
      {
        println("Letters now have distinct values.")
      }

      val solution = letters.map(_.value)
      p("s,e,n,d,m,o,r,y", solution)

      // val m = ((m : Map[Letter,Int]) => true).lazySolve
      // for(l <- letters) {
      //   assuming(m(l) >= 0 && m(l) <= 9) {
      //     println("OK for " + l)
      //   }

      //   // we need this too because S and M occur as most significant digits
      //   if (l == S() || l == M()) assuming(m(l) >= 1) {
      //     println(l + " greater than 0  OK")
      //   }
      // }

      // assuming( 
      //                      1000 * m(S()) + 100 * m(E()) + 10 * m(N()) + m(D()) +
      //                      1000 * m(M()) + 100 * m(O()) + 10 * m(R()) + m(E()) ==
      //     10000 * m(M()) + 1000 * m(O()) + 100 * m(N()) + 10 * m(E()) + m(Y())) {
      //   println("OK for sum")
      // }

      // assuming(distinct(m(S()), m(E()), m(N()), m(D()), m(M()), m(O()), m(R()), m(Y()))) {
      //   println("OK for distinct")
      // }
      // 
      // println("A solution : " + m.value)
    }
  }

  SendMoreMoney.run

  object Graphs {
    @spec sealed abstract class List
    @spec case class Cons(head : Int, tail : List) extends List
    @spec case class Nil() extends List

    @spec sealed abstract class OptInt
    @spec case class IntSome(value : Int) extends OptInt
    @spec case class None() extends OptInt

    @spec def contains(l : List, e : Int) : Boolean = l match {
      case Nil() => false
      case Cons(x,xs) => x == e || contains(xs,e)
    }

    //type Graph = Map[Int,List]
    @spec def hasEdge(g : Map[Int,List], src : Int, dst : Int) : Boolean = {
      if(g.isDefinedAt(src)) contains(g(src), dst) else false
    }

    @spec def validPath(g : Map[Int,List], path : List) : Boolean = path match {
      case Nil() => true
      case Cons(x, Nil()) => true
//      case Cons(x, xs @ Cons(y, _)) if (x == y) => validPath(g, xs)
      case Cons(x, xs @ Cons(y, _)) => hasEdge(g, x, y) && validPath(g, xs)
    }

    @spec def length(l : List) : Int = (l match {
      case Nil() => 0
      case Cons(_,xs) => 1 + length(xs)
    }) ensuring(_ >= 0)

    @spec def head(l : List) : OptInt = l match {
      case Nil() => None()
      case Cons(x,_) => IntSome(x)
    }

    @spec def tail(l : List) : OptInt = l match {
      case Nil() => None()
      case Cons(x,Nil()) => IntSome(x)
      case Cons(x,xs) => tail(xs)
    }

    def paths(g : Map[Int,List], src : Int, dst : Int) = {
      ((path : List) => 
        head(path) == IntSome(src) &&
        tail(path) == IntSome(dst) &&
        validPath(g, path)).minimizing(length(_ : List)).findAll
    }

    def run : Unit = {
      def mkList(vals : Int*) : List = vals.foldRight[List](Nil())((v,l) => Cons(v,l))
      val graph : Map[Int,List] = Map(
        1 -> mkList(2,3),
        2 -> mkList(3),
        3 -> mkList(4),
        4 -> mkList(1))

      // That crashes somehow...
      //p("Paths from 1 to 4, in order of length", paths(graph, 1, 4).toList)

      ((g : Map[Int,List], p : List) => validPath(g, p) && length(p) == 10).find
    }
  }

  //Graphs.run
}
