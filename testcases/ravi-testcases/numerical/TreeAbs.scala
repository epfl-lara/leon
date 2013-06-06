object CompleteTreeAbs
{
  def twopower(x: Int) : Int = {
    
    if(x < 1) 1    
    else      
      2* twopower(x - 1)
      
  } ensuring (res => res >= 1)
  
  /*def log2(x: Int) : Int = (
      if (x < 1)  -1
      else if(x == 1) 0
      else log2R(x,1,0)            
  )
  
  def log2R(x: Int, y: Int, i: Int): Int = (
      if(2 * y > x) i - 1 
      else log2R(x, 2*y, i + 1)
  )*/
    
  // Returns the height
  def ins(s: Int, h: Int): Int = {
    require(s >= twopower(h) - 1 && s >=0 && h >=0)
    
    if(s == 0) 1
    else{
      val h2 = ins(s - twopower(h-1),h-1) + 1
      val s2 = s + 1
      //balance(s2,h2)
      h2
    }    
  }                        
  
  def add(s: Int, h: Int): Int = {
    require(s >= twopower(h) - 1 && s >=0 && h >=0)
    
    ins(s,h)
    
  } ensuring(res => s+1 >= twopower(res) - 1)                
  
  /*def balance(s: Int, h: Int): Int = {        
    if(s < twopower(h)) log2(s)
    else s
  }*/ 
} 