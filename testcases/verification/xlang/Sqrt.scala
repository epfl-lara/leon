import leon.lang._

object Sqrt {

  def isqrt(num0: Int): Int = {
    require(num0 >= 0)
    var num = num0
    var res: Int = 0
    var bit: Int = 1 << 30 // The second-to-top bit is set: 1 << 30 for 32 bits
  
    // "bit" starts at the highest power of four <= the argument.
    while (bit > num) {
      bit >>= 2
    }

    (while (bit != 0) {
       if (num >= res + bit) {
         num = num - (res + bit)
         res = (res >> 1) + bit
       } else {
        res >>= 1
       }
       bit >>= 2
    }) invariant (res * res <= num0)

    res
  } ensuring (res => res * res <= num0 && (res + 1)*(res + 1) > num0) 

  def buggyIsqrt(num0: Int): Int = {
    require(num0 >= 0)
    var num = num0
    var res: Int = 0
    var bit: Int = 1 << 30 // The second-to-top bit is set: 1 << 30 for 32 bits
  
    // "bit" starts at the highest power of four <= the argument.
    while (bit > num) {
      bit >>= 2
    }

    (while (bit != 0) {
       if (num >= res + bit) {
         num = num - res + bit //bug here, missing parenthesis
         res = (res >> 1) + bit
       } else {
         res >>= 1
       }
       bit >>= 2
    }) invariant (res * res <= num0)

    res
  } ensuring (res => res * res <= num0 && (res + 1)*(res + 1) > num0) 

}
