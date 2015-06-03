
/*
This function terminates for all inputs, see
http://en.wikipedia.org/wiki/McCarthy_91_function

But the termination checker returns NoGuarantee after 75s.
*/
object McCarthy91 {
  def M(n: BigInt): BigInt = if (n > 100) n-10 else M(M(n+11))
}
