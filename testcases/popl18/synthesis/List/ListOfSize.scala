import leon.annotation._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object ListOfSize {

  def listOfSize(s: BigInt): List[BigInt] = {
    require(s >= 0)
    choose((l: List[BigInt]) => l.size == s)
  }
}
