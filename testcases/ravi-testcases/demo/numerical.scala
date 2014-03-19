import leon.Utils._

object SeeSaw
{
	def s(x: Int, y : Int) : Int =  {	  
	  require(y >=0)
	  
	  if(x <= 4) {
	    s(x+1,y+2)
	  }
	  else if(x >=7 && x <= 9){
	    s(x+1,y+3)
	  }
	  else if(x >= 100){
	    y
	  }
	  else {
	    s(x+2,y+1)
	  }
	} ensuring(res => (100 - x  <= 2*res) )		
} 