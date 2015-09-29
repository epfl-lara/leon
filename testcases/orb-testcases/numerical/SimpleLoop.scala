object SimpleLoop
{
	def s(x: BigInt) : BigInt = {
	  if(x < 0)
	    BigInt(0)
	  else
	    s(x-1) + 1
	} ensuring(res => res != -1)
}