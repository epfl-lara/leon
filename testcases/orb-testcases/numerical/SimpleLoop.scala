import leon.collection._
object SimpleLoop
{
	/*def s(x: BigInt) : BigInt = {
	  if(x < 0)
	    BigInt(0)
	  else
	    s(x-1) + 1
	} ensuring(res => res != -1)*/
  
  def s(x: List[BigInt]): BigInt = {
    x match {
      case Cons(h, tail) => 
        val y = h + 1
        val z = s(tail)
        y + z
    }    
  }
}