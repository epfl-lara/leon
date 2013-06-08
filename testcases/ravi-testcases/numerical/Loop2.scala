import leon.Utils._
object Loop2
{
	def s(x: Int) : Int = {
	  if(x < 0)
	    0 - x
	  else 
	    s(x-1) + x	    
	} ensuring(res => res != -1 template((a : Float, b : Float, c: Float) => (a*res + b*x + c <= 0 && b < 0)))	
	//inductive generalization res >= 0
} 