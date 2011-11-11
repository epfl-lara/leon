import cp.Definitions._
import cp.Terms._
import cp.LTrees._

// This file contains examples from the paper:
//     A.S. Köksal, V. Kuncak, P. Suter, "Constraints as Control", POPL 2012
//   as well as some more.
// The file should be compiled and run with Scala 2.9+ along with the Kaplan
// plugin.

object ACMDLExamples extends App {
  def p(str : String, a : =>Any) : Unit = {
    println(str + " : " + a.toString)
  }

  trait Demo {
    val name : String
    def action : Unit
    def run : Unit = {
      println("*** Running " + name + " ***")
      action
    }
  }

  object Initial extends Demo {
    val name = "first examples"
    val c1 : Constraint2[Int,Int] = ((x : Int, y : Int) => 2 * x + 3 * y == 10 && x >= 0 && y >= 0)
    def action : Unit = {
      p("c1(2,1)", c1(2,1))
      p("c1(5,0)", c1(5,0))
      p("c1.solve", c1.solve)
      p("c1.findAll.toList", c1.findAll.toList)
      p("bounded(3).findAll.toList", bounded(3).findAll.toList)
    }
  }
  Initial.run

  def bounded(m : Int) : Constraint1[Int] = ((x : Int) => x >= 0 && x <= m)

  object Matrices extends Demo {
    val name = "unimodular matrices"
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
      boundedQ(m) && (isUnimodular _)
    }
  
    def action : Unit = {
      p("Unimodular count", (0 to 5).map(boundedUnimodular(_).findAll.size).toList)
      p("boundedUnimodular(2).findAll.take(5).foreach.println(_))", boundedUnimodular(2).findAll.take(5).toList.map(_.toString))
      p("inverse of(4,5,3,4): ", inverse(4,5,3,4))
      p("inverse of(4,5,3,0): ", inverse(4,5,3,0))
    }
  }
  Matrices.run

  object SatSolving extends Demo {
    val name = "sat solving"
    def satSolve(problem : Seq[Seq[Int]]) = {
      problem.map(l => l.map(i => {
        val id = scala.math.abs(i)
        val isPos = i > 0
        val c : Constraint1[Map[Int,Boolean]] = ((m : Map[Int,Boolean]) => m(id) == isPos)
        c
      }).reduceLeft(_ || _)).reduceLeft(_ && _).find
    }

    def action : Unit = {
      println("satSolve(p)", satSolve(Seq(Seq(1,-2,-3), Seq(2,3,4), Seq(-1,-4))))
      println("satSolve(Seq(Seq(1,2), Seq(-1), Seq(-2)))", satSolve(Seq(Seq(1,2), Seq(-1), Seq(-2))))
    }
  }
  SatSolving.run

  object Knapsack extends Demo {
    val name = "knapsack"

    def action : Unit = {
      val values  : List[Int] = List(4, 2, 2, 1, 10)
      val weights : List[Int] = List(12, 1, 2, 1, 4)
      val maxWeight : Int = 15

      def conditionalSumTerm(values : List[Int]) : IntTerm1[Map[Int,Boolean]] = {
        values.zipWithIndex.map(pair => {
          val (value,index) = pair
          ((m : Map[Int,Boolean]) => (if(m(index)) value else 0)).i
        }).reduceLeft(_ + _)
      }
      val valueFunction = conditionalSumTerm(values.map(x => -x))
      val weightFunction = conditionalSumTerm(weights)
      val answer = ((x : Int) => x <= maxWeight)
        .compose0(weightFunction)
        .minimizing(valueFunction)
        .find

      p("Knapsack map", answer)
    }
  }
  Knapsack.run

  object Primes extends Demo {
    val name = "prime numbers"

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
  
    def action : Unit = {
      println("Primes")
      primes.take(10).foreach(println(_))
    }
  }
  Primes.run

  object RedBlackTrees extends Demo {
    val name = "red-black trees"

    @spec sealed abstract class Color
    @spec case class Red() extends Color
    @spec case class Black() extends Color
    
    @spec sealed abstract class Tree
    @spec case class Node(c : Color, l : Tree, v : Int, r : Tree) extends Tree
    @spec case class Leaf() extends Tree

    @spec sealed abstract class OptionInt
    @spec case class SomeInt(v : Int) extends OptionInt
    @spec case class NoneInt() extends OptionInt

    @spec def size(t : Tree) : Int = (t match {
      case Leaf() => 0
      case Node(_, l, _, r) => 1 + size(l) + size(r)
    }) ensuring(_ >= 0)

    @spec def blackBalanced(t : Tree) : Boolean = t match {
      case Node(_,l,_,r) => blackBalanced(l) && blackBalanced(r) && blackHeight(l) == blackHeight(r)
      case Leaf() => true
    }

    @spec def isBlack(t: Tree) : Boolean = t match {
      case Leaf() => true
      case Node(Black(),_,_,_) => true
      case _ => false
    }
  
    @spec def redNodesHaveBlackChildren(t: Tree) : Boolean = t match {
      case Leaf() => true
      case Node(Black(), l, _, r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
      case Node(Red(), l, _, r) => isBlack(l) && isBlack(r) && redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
    }

    @spec def blackHeight(t : Tree) : Int = t match {
      case Leaf() => 0
      case Node(Black(), l, _, _) => blackHeight(l) + 1
      case Node(Red(), l, _, _) => blackHeight(l)
    }

    @spec def validColoring(t : Tree) : Boolean = {
      isBlack(t) && redNodesHaveBlackChildren(t) && blackBalanced(t) 
    }

    @spec def valuesWithin(t : Tree, bound : Int) : Boolean = t match {
      case Leaf() => true
      case Node(_,l,v,r) => 0 < v && v <= bound && valuesWithin(l,bound) && valuesWithin(r,bound)
    }

    @spec def orderedKeys(t : Tree) : Boolean = orderedKeys(t, NoneInt(), NoneInt())

    @spec def orderedKeys(t : Tree, min : OptionInt, max : OptionInt) : Boolean = t match {
      case Leaf() => true
      case Node(c,a,v,b) =>
        val minOK = 
          min match {
            case SomeInt(minVal) =>
              v > minVal
            case NoneInt() => true
          }
        val maxOK =
          max match {
            case SomeInt(maxVal) =>
              v < maxVal
            case NoneInt() => true
          }
        minOK && maxOK && orderedKeys(a, min, SomeInt(v)) && orderedKeys(b, SomeInt(v), max)
    }

    @spec def validTree(t : Tree) : Boolean = {
      validColoring(t) && orderedKeys(t) 
    }

    def action : Unit = {
      (1 to 3).foreach(i => {
        val num = ((t : Tree) => validTree(t) && valuesWithin(t,i) && size(t) == i).findAll.size
        p("# of RBTs with " + i + " distinct els", num)
      })
    }
  }
  RedBlackTrees.run

  object SendMoreMoney extends Demo {
    val name = "SEND+MORE=MONEY"

    def asserting(c : Constraint0) : Unit = {
      var entered = false
      for(i <- c.lazyFindAll) {
        entered = true
      }
      if(!entered) { throw new Exception("Asserting failed.") }
    }

    def action : Unit = {
      val anyInt : Constraint1[Int] = ((n : Int) => true)

      val letters @ Seq(s,e,n,d,m,o,r,y) = Seq.fill(8)(anyInt.lazySolve)

      for(l <- letters) {
        asserting(l >= 0 && l <= 9) 
      }

      asserting(s >= 1)
      asserting(m >= 1) 

      when(distinct[Int](s,e,n,d,m,o,r,y)) {
        println("Letters now have distinct values.")
      } otherwise {
        println("Letters can't have distinct values.")
      }

      val fstLine = anyInt.lazySolve
      val sndLine = anyInt.lazySolve
      val total = anyInt.lazySolve

      asserting(fstLine == 1000*s + 100*e + 10*n + d)
      asserting(sndLine == 1000*m + 100*o + 10*r + e)
      asserting(total   == 10000*m + 1000*o + 100*n + 10*e + y)
      when(total == fstLine + sndLine) {
        println("The puzzle has a solution : " + letters.map(_.value) + " (" + fstLine.value + " + " + sndLine.value + " = " + total.value + ")")
      } otherwise {
        println("The puzzle has no solution.")
      }
    }
  }
  SendMoreMoney.run

  object Calendar extends Demo {
    // Declaratively computes a year and extra number of days since January first 1980.
    // A piece of (imperative) code performing the same computation was responsible
    // for a bug in a popular Mp3 player.
  
    val name = "Date computation"

    final val totalDays = 10593
    final val originYear = 1980
  
    @spec def leapDaysUntil(y: Int) = (y - 1) / 4 - (y - 1) / 100 + (y - 1) / 400
  
    val (year, day) = ((year: Int, day: Int) => 
      totalDays == (year - originYear) * 365 + leapDaysUntil(year) - leapDaysUntil(originYear) + day &&
      day > 0 && day <= 366).solve
  
    def action : Unit = {
      println("Year : %d, day : %d" format (year, day))
    }
  }
  Calendar.run
}
