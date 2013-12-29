import leon.Utils._
import scala.collection.immutable.Map

object ObsPure {
  
  //An example with caching  
  /**
   * This procedure produces no result
   */
  def f(x : Int, instate: Map[Int,Int]): (Int, Map[Int,Int]) = {
    if(instate.isDefinedAt(x)) {
      val y = instate(x)
      (y, instate)
    }
    else {
      val res = fact(x)
      (res, instate.updated(x, res))
    }
  }
  
  def fact(x: Int): Int = {    
    if(x <= 0) 1
    else x * fact(x-1)
  }
  
  //havocs the state. Asserts that the cache consistency is preserved
  def havoc(x : Int, instate: Map[Int,Int]): Map[Int,Int] = {    
    require(!instate.isDefinedAt(x) || instate(x) == fact(x))
    
    if (nondet[Boolean]) {      
      val (_, next_state) = f(nondet[Int], instate)
      havoc(x, next_state)      
    } else {
      instate
    }
  } ensuring(res => !res.isDefinedAt(x) || res(x) == fact(x))
  
  def init() : Map[Int, Int] = {
    scala.Predef.Map[Int,Int](0 -> 1)
  }
 
  def purityChecker(): (Int, Int) = {
    
    val x = nondet[Int]
    val some_state = havoc(x, init())
    val (res1, next_state) = f(x, some_state)
    val later_state = havoc(x, next_state)
    val (res2, _) = f(x, later_state)
    (res1, res2)

  } ensuring (res => res._1 == res._2)
}
