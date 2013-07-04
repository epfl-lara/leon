import leon.Utils._

object ListAppendAbs
{	
	def app(x: Int) : Int = {
	  require(x >=0)
	  	  
	  app0(x,1) 
	    
	} ensuring(res => res == x + 1)
	
	def app0(a: Int, b: Int) : Int = {
	  require(a >=0 && b >=0)
	  
	  if(a <= 0)
	    b
	  else
	    app0(a-1,b+1)	    
	} ensuring(res => true template((p : Float, q : Float, r: Float) => (p*res + q*a + r*b == 0 && q >= -1 && r >= -1)))
} 
