import leon.invariant._
import leon.instrumentation._

object InsertionSort {
  abstract class List
  
  case class Cons(head : BigInt, tail : List) extends List
  
  case class Nil() extends List
  
  def size(l : List): BigInt = l match {
    case Cons(_, xs) =>
      BigInt(1) + size(xs)
    case _ =>
      BigInt(0)
  }
  
  def sortedInstimedepth(e : BigInt, l : List): (List, BigInt, BigInt) = {
    val bd = l match {
      case Cons(x, xs) =>
        val c11 = BigInt(1)
        val expr = if (x <= e) {
          val e19 = sortedInstimedepth(e, xs)
          (Cons(x, e19._1), BigInt(4) + e19._2, {
            val mt = BigInt(2) + e19._3
            if (c11 >= mt) {
              c11
            } else {
              mt
            }
          })
        } else {
          (Cons(e, l), BigInt(3), if (BigInt(1) >= c11) {
            BigInt(1)
          } else {
            c11
          })
        }
        (expr._1, BigInt(4) + expr._2, BigInt(1) + expr._3)
      case _ =>
        (Cons(e, Nil()), BigInt(4), BigInt(3))
    }
    (bd._1, bd._2, bd._3)
  }
  
  def sorttimerec(l : List): (List, BigInt, BigInt) = {
    val bd1 = l match {
      case Cons(x, xs) =>
        val e30 = sorttimerec(xs)
        val e28 = sortedInstimedepth(x, e30._1)
        (e28._1, (BigInt(6) + e28._2) + e30._2, BigInt(1) + e30._3)
      case _ =>
        (Nil(), BigInt(3), BigInt(0))
    }
    (bd1._1, bd1._2, bd1._3)
  }

  def main(args: Array[String]): Unit = {
    import scala.util.Random
    import java.io._

    val rand = Random

    val sr = new File("sort-runnable.data")
    val so1 = new File("sort-orb1.data")
    val so2 = new File("sort-orb2.data")
    val sir = new File("sortins-runnable.data")
    val sio1 = new File("sortins-orb1.data")
    val sio2 = new File("sortins-orb2.data")

    
    val pwl = List(sr, so1, so2, sir, sio1, sio2).map(a => new PrintWriter(new FileOutputStream(a)))

    ((10 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)).foreach { i =>
      val ls: List = {
        (1 to i).foldLeft[List](Nil()) {
          case (acc, curr) =>
            val x = rand.nextInt(10)
            Cons(x, acc)
        }
      }


      val sortset1 = (11 * i * i + 4)
      val sortinsset1 = 8*i + 4
      val sortset2 = 4*i*i + 6*i + 3
      val sortinsset2 = 8*i + 4

      pwl(0).println(i + " " + sorttimerec(ls)._2)
      pwl(1).println(i + " " + sortset1)
      pwl(2).println(i + " " + sortset2)
      pwl(3).println(i + " " + sortedInstimedepth(11, ls)._2)
      pwl(4).println(i + " " + sortinsset1)
      pwl(5).println(i + " " + sortinsset2)
    }

    pwl.foreach(pw => pw.close())
  }
}
