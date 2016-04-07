import leon.lang._
import leon.lang.xlang._
import leon.util.Random

object GuessNumber {
  
  def pickRandomly(min: BigInt, max: BigInt): BigInt = {
    require(min >= 0 && max >= min)
    Random.nextBigInt(max - min + 1) + min
  }

  def main(): Unit = {
    val choice = pickRandomly(0, 10)

    var guess = pickRandomly(0, 10)
    var top: BigInt = 10
    var bot: BigInt = 0

    (while(bot < top) {
      if(isGreater(guess, choice)) {
        top = guess-1
        guess = pickRandomly(bot, top)
      } else if(isSmaller(guess, choice)) {
        bot = guess+1
        guess = pickRandomly(bot, top)
      }
    }) invariant(guess >= bot && guess <= top && bot >= 0 && top <= 10 && bot <= top && choice >= bot && choice <= top)
    val answer = bot
    assert(answer == choice)
  }

  def isGreater(guess: BigInt, choice: BigInt): Boolean = guess > choice
  def isSmaller(guess: BigInt, choice: BigInt): Boolean = guess < choice

}
