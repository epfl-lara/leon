import leon.invariant._

object ListAppendAbs
{
	def app(x: BigInt) : BigInt = {
	  require(x >=0)

	  app0(x,1)

	} ensuring(res => res == x + 1)

	def app0(a: BigInt, b: BigInt) : BigInt = {
	  require(a >=0 && b >=0)

	  if(a <= 0)
	    b
	  else
	    app0(a-1,b+1)
	} ensuring(res => tmpl((p, q, r) => (p*res + q*a + r*b == 0 && q  != 0)))
}
