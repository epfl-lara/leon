import leon.lang.invariantLang._
object UIFTest
{  
	def s(x: Int, y: Int) : Int = {
	  require(x == -y)
	  
	  if(x < 0)
	  {
	    makePositive(x)
	  }
	  else 
	    s(x-1,y+1) + 1
	    
	}ensuring(res => res != makePositive(-y) - 1 template((a,b,c) => a*res + b*makePositive(-y) + c <= 0 && a < 0 && b >0)) 
	//ensuring(res => res != makePositive(-y) - 1 template((a,b,c) => a*res + b*makePositive(-y) + c <= 0 && a == -b))
	//ensuring(res => res >= makePositive(-y))		
	
	def makePositive(x : Int) : Int = {
	  -x
	}	
} 
