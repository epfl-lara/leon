package leon

package object math {

  def min(i1: Int, i2: Int) = if (i1 <= i2) i1 else i2
  def max(i1: Int, i2: Int) = if (i1 >= i2) i1 else i2
  def min(i1: BigInt, i2: BigInt) = if (i1 <= i2) i1 else i2
  def max(i1: BigInt, i2: BigInt) = if (i1 >= i2) i1 else i2

}
