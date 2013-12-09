import leon.Utils._

object ObsPure {
  
/*    def f(global: Int, flag: Boolean) : (Int, Boolean)  = {
      if(!flag) {       
        (global + 1, flag) 
      } else {
        (global, flag)
      }
    }
    
    def g( global: Int, flag: Boolean) : (Int, Boolean) = {
      (global, true)
    }
        
    def havoc(global: Int, flag: Boolean) : (Int, Boolean) = {
      
      if(nondet) {
        
        val next_state = f(global, flag)
        havoc(next_state._1, next_state._2)
         
      } else {
        (global, g(global, flag)._2)
      }
    }
    
    def purityChecker(): (Int, Int) = {
      
      val some_state = havoc(0, false)
      val (res1, flag1) = g(some_state._1, some_state._2)
      val someother_state = havoc(some_state._1, flag1)
      val res2 = g(someother_state._1, someother_state._2)._1
      (res1, res2)
      
    } ensuring(res => res._1 == res._2)
*/    
        
    def havoc(x: Int) : Int = {      
      
      val y = nondet[Boolean]
      if(x>=0) {
        if(y) havoc(x-1)
        else 0
      }       
      else if(!y && x < 0) {
        -1
      } else 0
      
    } //ensuring(res => res >= 0)
    
    def purityChecker(): Int ={
      havoc(0)
    } ensuring(_ >= 0)
}
