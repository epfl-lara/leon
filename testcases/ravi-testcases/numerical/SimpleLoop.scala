import leon.Utils._

object SimpleLoop
{
	def s(x: Int) : Int = {
	  if(x < 0)
	    0
	  else 
	    s(x-1) + 1
	    
	} ensuring(res => res != -1)	
	//inductive generalization res >= 0
	
	def always(i : Int) : Boolean =  {
	  (i >= 0)
	} holds
} 