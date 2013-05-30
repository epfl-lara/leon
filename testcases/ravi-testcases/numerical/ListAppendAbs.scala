object ListAppendAbs
{
	def app(x: Int) : Int = {
	  require(x >=0)
	  
	  val y = 1
	  app0(x,y) 
	    
	} ensuring(res => res <= x + 1)
	
	def app0(a: Int, b: Int) : Int = {
	  require(a >=0 && b >=0)
	  
	  if(a == 0)
	    b
	  else
	    1 + app0(a-1,b)	    
	} //ensuring(res => (-1 - 4 * a  - 6 * b + res * 4) <= 0)
} 