import leon.invariant._
import leon.annotation._

object LogarithmTest {
  
  @monotonic
  def log(x: BigInt) : BigInt = {
    require(x >= 0)    
    if(x <= 1) 0
    else {      
      1 + log(x/2)    
    }    
  }   
    
  def binarySearchAbs(x: BigInt, min: BigInt, max: BigInt): BigInt = {
    require(max - min >= 0)
    if (max - min <= 0) 2    	
    else {
      val mid = (min + max) / 2
      if (x < mid) {
        binarySearchAbs(x, min, mid) + 5
      } else if (x > mid) {
        binarySearchAbs(x, mid + 1, max) + 7
      } else
        8
    }                	 
  } ensuring(res => tmpl((a,b) => res <= a*log(max - min) + b))
} 
