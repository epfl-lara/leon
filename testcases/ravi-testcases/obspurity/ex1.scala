import leon.Utils._

object ObsPure {
  /**
   * This procedure produces no result
   */
  def f(instate: (Int, Boolean)): (Int, Boolean) = {
    val (global, flag) = instate
    if (!flag) {
      (global + 1, flag)
    } else {
      (global, flag)
    }
  }

  /**
   * This procedure produces one result that is of Int type
   */
  def g(instate: (Int, Boolean)): (Int, (Int, Boolean)) = {
    val (global, _) = instate
    (global, (global, true))
  }

  //this procedure produces no result
  def havoc(instate: (Int, Boolean)): (Int, Boolean) = {
    if (nondet[Boolean]) {
      val next_state = f(instate)
      havoc(next_state)
    } else if(nondet[Boolean]) {
      val (_, next_state) = g(instate)
      havoc(next_state)
    } else {
      instate
    }
  } ensuring(res => !instate._2 || (res == instate))
  
  def init() : (Int, Boolean) = {
    (0, false)
  }

  def purityChecker(): (Int, Int) = {
    
    val some_state = havoc(init())    
    val (res1, next_state) = g(some_state)
    val later_state = havoc(next_state)
    val (res2, _) = g(later_state)
    (res1, res2)

  } ensuring (res => res._1 == res._2)
}
