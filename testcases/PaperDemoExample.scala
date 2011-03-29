object PaperDemoexample {
    sealed abstract class List
    case class Cons(head: Int, tail: List) extends List
    case class Nil() extends List

    def size(l: List) : Int = (l match {
        case Nil() => 0
        case Cons(_, t) => 1 + size(t)
    })

    def sizeTailRec(l: List) : Int = sizeAcc(l, 0)
    def sizeAcc(l: List, acc: Int) : Int = {
     require(acc >= 0)
     l match {
       case Nil() => acc
       case Cons(_, xs) => sizeAcc(xs, acc+1)
     }
    } ensuring(res => res == size(l) + acc)
}
