import leon.annotation._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object Insert {

  //def insert(in1: List, v: BigInt): List = {
  //  Cons(v, in1)
  //} ensuring { content(_) == content(in1) ++ Set(v) }

  def insert[A](in1: List[A], v: A) = choose {
    (out : List[A]) =>
      out.content == in1.content ++ Set(v)
  }
}
