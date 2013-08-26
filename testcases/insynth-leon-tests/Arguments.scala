import leon.Annotations._
import leon.Utils._

object Hole { 
  
  def method(t: Int, x: Boolean, y: Boolean) : Int = ({
    if (t > 5)    
    	hole(5)
  	else 
  	  t
  }) ensuring ( _ > 0 )

}
