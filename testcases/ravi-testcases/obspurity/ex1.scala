import leon.Utils._

object ObsPure {
  
    def f(global: Int, flag: Boolean) : (Int, Boolean)  = {
      if(!flag) {       
        (global + 1, flag) 
      } else {
        (global, flag)
      }
    }
    
    def g( global: Int, flag: Boolean) : (Int, Boolean) = {
      (global, true)
    }
    
    def select(nondet: Int) : Boolean = {
      (nondet >= 0)
    }
    
    def update(nondet: Int) : Int = {
      -nondet
    }
    
    def havoc(global: Int, flag: Boolean, nondet: Int) : (Int, Boolean) = {
      
      if(select(nondet)) {
        
        val next_state = f(global, flag)
        havoc(next_state._1, next_state._2, update(nondet))
         
      } else {
        (global, g(global, flag)._2)
      }
    }
    
    def purityChecker(nondet: Int): (Int, Int) = {
      
      val some_state = havoc(0, false, nondet)
      val (res1, flag1) = g(some_state._1, some_state._2)
      val someother_state = havoc(some_state._1, flag1, nondet)
      val res2 = g(someother_state._1, someother_state._2)._1
      (res1, res2)
      
    } ensuring(res => res._1 == res._2)
    
}
