import leon.annotation._
import leon.annotation.grammar._
import leon.lang._
import leon.lang.synthesis._
import leon.grammar.Grammar._
import leon.collection._

object Union {

  def union[A](in1: List[A], in2: List[A]) = choose {
    (out : List[A]) =>
      out.content == in1.content ++ in2.content
  }
}
