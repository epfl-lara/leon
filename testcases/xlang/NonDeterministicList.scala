import leon.lang._

object NonDeterminism {

  abstract class IntList
  case class Cons(h: Int, tail: IntList) extends IntList
  case class Nil() extends IntList

  def insert(l: IntList, el: Int): IntList = Cons(el, l)
  def remove(l: IntList, el: Int): IntList = l match {
    case Cons(x, xs) => 
      if(x < el) Cons(x, remove(xs, x)) 
      else if(x == el) remove(xs, x) 
      else  xs
    case Nil() => Nil()
  }

  def content(l: IntList) : Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(x, xs) => Set(x) ++ content(xs)
  }

  def nonDeterministicExecution(): Boolean = {

    var list: IntList = Cons(42, Nil())
    var error: Boolean = false

    val b1 = epsilon((x: Boolean) => true)
    val n1 = epsilon((x: Int) => true)
    if(b1)
      list = insert(list, n1)
    else {
      list = remove(list, n1)
      if(content(list).contains(n1)) {
        error = true
      }
    }

    val b2 = epsilon((x: Boolean) => true)
    val n2 = epsilon((x: Int) => true)
    if(b2)
      list = insert(list, n2)
    else {
      list = remove(list, n2)
      if(content(list).contains(n2)) {
        error = true
      }
    }

    !error
  } holds

}
