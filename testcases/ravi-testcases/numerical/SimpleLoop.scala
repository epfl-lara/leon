import leon.Utils._

object SimpleLoop
{
	def s(x: Int) : Int = {
	  if(x < 0)
	    0
	  else 
	    s(x-1) + 1
	    
	} ensuring(res => res != -1 template((a : Float, b : Float, c: Float) => a*res + b*x + c <= 0))	
	//inductive generalization res >= 0	
} 