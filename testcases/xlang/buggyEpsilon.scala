import leon.lang._

object Test {

  abstract class SortedList
  case class Cons(head: Int, tail: SortedList) extends SortedList
  case class Nil() extends SortedList

  def content(l: SortedList): Set[Int] = l match {
    case Cons(head, tail) => content(tail) ++ Set(head)
    case Nil() => Set()
  }

  def insert(x: Int, l: SortedList): SortedList = Cons(x, l)

  def remove(x: Int, l: SortedList): SortedList = {
    //require(pos(l) && sorted(l, 0))
    l match {
      case Cons(head, tail) => if(head == x) remove(x, tail) else if(head < x) Cons(head, remove(x, tail)) else l
      case Nil() => Nil()
    }
  } //ensuring(res => !content(res).contains(x))

  def sorted(l: SortedList, prec: Int): Boolean = l match {
    case Cons(head, tail) => if(prec <= head) sorted(tail, head) else false
    case Nil() => true
  }
  def pos(l: SortedList): Boolean = l match {
    case Cons(head, tail) => if(head < 0) false else pos(tail)
    case Nil() => true
  }



  def nonDeterministicList(): Boolean = {
    var i = 0
    var b = epsilon((x: Boolean) => i==i)
    var b2 = false
    var n = 0
    var list: SortedList = Nil()
    var error = false

    //(while(b) {
      i = i + 1
      b = epsilon((x: Boolean) => i==i)
      b2 = epsilon((x: Boolean) => i==i)
      n = epsilon((x: Int) => x >= 0)
      if(b2)
        list = insert(n, list)
      else {
        list = remove(n, list)
        if(content(list).contains(n))
          error = true
      }
      i = i + 1
      b = epsilon((x: Boolean) => i==i)
      b2 = epsilon((x: Boolean) => i==i)
      n = epsilon((x: Int) => x >= 0)
      if(b2)
        list = insert(n, list)
      else {
        list = remove(n, list)
        if(content(list).contains(n))
          error = true
      }
      i = i + 1
      b = epsilon((x: Boolean) => i==i)
      b2 = epsilon((x: Boolean) => i==i)
      n = epsilon((x: Int) => x >= 0)
      if(b2)
        list = insert(n, list)
      else {
        list = remove(n, list)
        if(content(list).contains(n))
          error = true
      }
    //}) //invariant(pos(list) && sorted(list, 0))
    error
  } ensuring(err => !err) //ensuring(_ == Nil())

}
