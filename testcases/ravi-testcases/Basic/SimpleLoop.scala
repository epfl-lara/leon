object SimpleLoop
{
	def s(x: Int) : Int = {
	  if(x < 0)
	    0
	  else 
	    s(x-1) + 1
	    
	} ensuring(res => res != -1)	
	//inductive generalization res >= 0
} 