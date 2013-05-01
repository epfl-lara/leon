object SimpleInterProc
{  
	def s(x: Int) : Int = {	  	  
	  if(x < 0)
	    makePositive(x)
	  else 
	    s(x-1) + 1
	    
	} ensuring(res => res != -1)	
	//inductive generalization res >= 0
	
	def makePositive(x : Int) : Int = {
	  2*negate(x)
	}
	def negate(c : Int) : Int={
	  -c
	}
} 