import leon.Utils._
import leon.Annotations._

object LogarithmTest {
  
  @monotonic
  def log(x: Int) : Int = {
    require(x >= 0)    
    if(x <= 1) 0
    else {      
      1 + log(x/2)    
    }    
  }
  
  def logFour(x: Int) : Int = {
    require(x >= 0)
    if(x <= 1) 0 
    else {
      1 + logFour(x/3)
    }
  } ensuring(res => true template((a,b) => time <= a*log(x) + b))
  
  @monotonic
  def ceillog(x: Int) : Int = {
    require(x >= 0)    
    if(x <= 1) 0
    else {      
      1 + ceillog(x - x/2)    
    }    
  }
  
  def mergeSortAbs(x: Int):Int = {
    require(x >=0)    
    if(x <= 1) x
    else {
      val k = x/2   
      mergeSortAbs(k) + mergeSortAbs(x-k)      
    }                	 
  } ensuring(res => true template((a,b) => time <= a*(x*ceillog(x)) + b))
} 
