object Loop2
{
	def s(x: Int) : Int = {
	  if(x < 0)
	    0 - x
	  else 
	    s(x-1) + x
	    
	} ensuring(res => res != -1)	
	//inductive generalization res >= 0
} 