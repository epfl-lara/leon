object SimpleInterProc
{
	def s(x: BigInt) : BigInt = {
	  if(x < 0)
	    makePositive(x)
	  else
	    s(x-1) + 1
	} ensuring(res => res != -1)

	def makePositive(y : BigInt) : BigInt = {
	  2*negate(y)
	}
	def negate(c : BigInt) : BigInt={
	  -c
	}
}