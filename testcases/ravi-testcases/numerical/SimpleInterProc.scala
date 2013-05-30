object SimpleInterProc
{  
	def s(x: Int) : Int = {	  	  
	  if(x < 0)
	    makePositive(x)
	  else 
	    s(x-1) + 1
	    
	} ensuring(res => res != -1)	
	//inductive generalization res >= 0
	
	def makePositive(y : Int) : Int = {
	  2*negate(y)
	}
	def negate(c : Int) : Int={
	  -c
	}
} 