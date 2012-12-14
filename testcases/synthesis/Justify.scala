import leon.Utils._

object Justify {

  abstract class IntList
  case class IntCons(head: Int, tail: IntList) extends IntList
  case class IntNil() extends IntList

  /*
   * The Science of Programming from David Gries Section 20.1
   
   * The goal is to justify a text. We are given a list of indices corresponding
   * to the columns of the starting point of each word. Each words are already
   * separated by one space. The parameter s is the additional number of spaces
   * at the end of the line that we will need to add between words. We
   * want the number of space on the same line to differ by at most one.
   *
   * If we denote by p and q the two number of spaces between words (p and q differ
   * only by 1), then we want to only switch once the number of space between words
   * on the line. This means that we first separate words using p, then we do it using
   * q until the end of the line. 
   *
   * z is the line number, the rule is for odd line number to have more spaces on the right (q=p+1)
   * and for even line number to have more spaces on the left (p=q+1). We do not want trailing
   * spaces.
   *
   * n is the number of words on the line.
   *
   * If we apply this justify to each line of a text separately, this should lead to a good looking
   * justified text.

   * Here is an example:
   *
   * justifying lines by
   * inserting extra blanks is
   * one task of a text editor.
   *
   * results in:
   *
   * justifying     lines     by
   * inserting extra  blanks  is
   * one  task of a text editor.
   */
  def justify(n: Int, z: Int, s: Int, words: IntList): IntList = {
    require(n >= 0 && s >= 0 && z >= 1)

    //here p and q are as defined above. t is used to find the index of the word where
    //we switch from p spaces to q spaces.
    val (res, p, q, t) = choose((justifiedWords: IntList, p: Int, q: Int, t: Int) => 
      p >= 0 && q >= 0 && p == q+1 && t >= 1 && t <= n && 
      p*(t-1) + q*(n-t) == s && //this constraint is probably going to be an issue since it is non linear
      ((z % 2 == 1 && q == p + 1) || (z % 2 == 0 && p == q + 1)) &&
      justifiedWords == addSpaces(words, p, q, t, n, 0) //this is likely to be problematic as well
    )

    res
  }

  def addSpaces(words: IntList, p: Int, q: Int, t: Int, n: Int, i: Int): IntList = words match {
    case IntNil() => IntNil()
    case IntCons(head, tail) =>
      if(i <= t) IntCons(head + p*(i-1), addSpaces(tail, p, q, t, n, i+1))
      else if(i > t && i <= n) IntCons(head + p*(t-1) + q*(i-t), addSpaces(tail, p, q, t, n, i+1))
      else IntNil() //this should never happen
  }

  /*
   * This version is a simpler one, in which we are just trying to determine parameters that can then
   * be mecanically used to build the justified text. Also we do not distinguish on even/odd line number.
   */
  def simpleJustify(n: Int, z: Int, s: Int, words: IntList): (Int, Int, Int) = {
    require(n >= 0 && s >= 0 && z >= 1)

    val (p, q, t) = choose((p: Int, q: Int, t: Int) => 
      p >= 0 && q >= 0 && p == q+1 && t >= 1 && t <= n && p*(t - 1) + q*(n-t) == s
    )

    //actually, we could simply use the parameter to program the ocnstruction of the List, rather than explicitly synthesizing it
    (p, q, t)
  }
}
