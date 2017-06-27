import leon.annotation._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object Delete {

  def delete(in: List[BigInt], v: BigInt) = {
    ???[List[BigInt]]
  } ensuring {
    (out : List[BigInt]) =>
      out.content == in.content -- Set(v)
  }
}
