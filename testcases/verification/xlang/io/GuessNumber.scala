import leon.lang._
import leon.lang.xlang._
import leon.io.StdIn

import leon.annotation._

object GuessNumber {

  @extern
  def pickBetween(bot: BigInt, top: BigInt): BigInt = {
    require(bot <= top)
    bot + (top - bot)/2  //works for execution
  } ensuring(res => res >= bot && res <= top)

  def guessNumber(choice: Option[BigInt])(implicit state: StdIn.State): BigInt = {
    require(choice match { case Some(c) => c >= 0 && c <= 10 case None() => true })
    var bot: BigInt = 0
    var top: BigInt = 10

    (while(bot < top) {
      val prevDec = top - bot

      val guess = pickBetween(bot, top-1) //never pick top, wouldn't learn anyting if pick top and if guess >= choice
      if(isSmaller(guess, choice)) {
        bot = guess+1
      } else {
        top = guess
      }
      val dec = top - bot
      assert(dec >= 0 && dec < prevDec)
    }) invariant(choice match {
      case Some(c) => bot >= 0 && top <= 10 && bot <= top && c >= bot && c <= top
      case None() => true
    })
    bot
  } ensuring(answer => choice match {
      case Some(c) => c == answer
      case None() => true
  })

  @extern
  def isGreater(guess: BigInt, choice: Option[BigInt])(implicit state: StdIn.State): Boolean = (choice match {
    case None() =>
      print("Is it (strictly) smaller than " + guess + ": ")
      StdIn.readBoolean
    case Some(c) => guess > c
  }) ensuring(res => choice match { case Some(c) => res == guess > c case None() => true })

  @extern
  def isSmaller(guess: BigInt, choice: Option[BigInt])(implicit state: StdIn.State): Boolean = (choice match {
    case None() =>
      print("Is it (strictly) greater than " + guess + ": ")
      StdIn.readBoolean
    case Some(c) => guess < c
  }) ensuring(res => choice match { case Some(c) => res == guess < c case None() => true })

  def guessNumberValid(choice: BigInt): BigInt = {
    require(choice >= 0 && choice <= 10)
    implicit val ioState = StdIn.newState
    guessNumber(Some(choice))
  } ensuring(_ == choice)

  @extern
  def main(args: Array[String]): Unit = {
    implicit val ioState = StdIn.newState
    println("Think of a number between 0 and 10...")
    println("Leon will try to guess it...")
    val answer = guessNumber(None())
    println("Found: " + answer)
    println("Goodbye")
  }

}
