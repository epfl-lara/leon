import leon.collection._
import leon.collection.List
import leon.lang._
import leon.proof.check
import leon.lang.synthesis._
import scala.language.postfixOps
import leon.annotation._

object MapRender {
  
  def f(i: Int): Map[Int, Int] = {
    Map(1 -> i)
  } ensuring {
    (m: Map[Int, Int]) => m(1) == 2
  }
  
  def g(m: Map[Int, Int]): Boolean = {
    !m.contains(0) || !m.contains(1)
  } holds
  
  def mapIntIntToString(in : Map[Int, Int]): String =  {
    Map.mkString(in, "MyMap(\n  "," -> ", ",\n  ", ")", (i:Int) => i.toString, (i:Int) => i.toString)
  }
}

