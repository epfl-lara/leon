import leon.Utils._

object NondetTest {
        
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
