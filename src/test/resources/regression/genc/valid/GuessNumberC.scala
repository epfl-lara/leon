import leon.lang._
import leon.lang.xlang._
import leon.io.StdIn

import leon.annotation._

// Based on xlang/io/GuessNumber.scala

object GuessNumberC {

  def pickBetween(bot: Int, top: Int): Int = {
    require(bot <= top && bot >= 0 && top <= 10)
    bot + (top - bot) / 2
  } ensuring(res => res >= bot && res <= top)

  def guessNumber()(implicit state: StdIn.State): Int = {
    var bot: Int = 0
    var top: Int = 10

    (while(bot < top) {
      val prevDec = top - bot

      val guess = pickBetween(bot, top - 1) // never pick top, wouldn't learn anyting
                                            // if pick top and if guess >= choice
      if (isSmaller(guess)) {
        bot = guess + 1
      } else {
        top = guess
      }
      val dec = top - bot
      assert(dec >= 0 && dec < prevDec)
    }) invariant(
      bot >= 0 && top <= 10 && bot <= top
    )

    bot
  }

  def isSmaller(guess: Int)(implicit state: StdIn.State): Boolean = {
    /*
     * NOTE: Pattern matching not supported by GenC
     * isSmallerImpl(guess, choice) match {
     *   case 0 => false
     *   case 1 => true
     * }
     */
    val answer = isSmallerImpl(guess)
    answer == 1
  }

  def isSmallerImpl(guess: Int)(implicit state: StdIn.State): Int = {
    // NOTE: scanning boolean is not yet supported by GenC
    // NOTE: string manipulation is not yet supported by GenC
    // print("Is it (strictly) greater than " + guess + " [0 = false, 1 = true]: ")
    print("Is is (strictly) greater than ")
    print(guess)
    print(" [0 == false, 1 == true]: ")

    val input = StdIn.readInt

    println()

    if (input == 0 || input == 1) input
    else isSmallerImpl(guess)
  } ensuring { res => res == 0 || res == 1 }

  def _main() = {
    println("Think of a number between 0 and 10...")
    println("Leon will try to guess it...")
    implicit val ioState = StdIn.newState
    val answer = guessNumber()
    print("Found: ")
    println(answer)
    println("Goodbye")
  }

  @extern
  def main(args: Array[String]): Unit = _main()

}
