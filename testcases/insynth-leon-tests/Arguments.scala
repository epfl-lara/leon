import leon.annotation._
import leon.lang._

object Hole { 
  
  def method(t: Int, x: Boolean, y: Boolean) : Int = ({
    if (t > 5)    
    	hole(5)
  	else 
  	  t
  }) ensuring ( _ > 0 )

}
