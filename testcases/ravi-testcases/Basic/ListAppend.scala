import leon.lang.invariantLang._

object ListWithSize {
    sealed abstract class List
    case class Cons(head: Int, tail: List) extends List
    case class Nil() extends List
     
    def size(l: List) : Int = {l match {         
        case Cons(_, t) => 1 + size(t)
        case _ => 0
    }} 
    //ensuring(res => true template((a) => a*res <= 0 ))    
    //ensuring(res => res >= 0 template((a) => true))
    //ensuring(res => true template((a) => a*res <= 0 ))

    def append(l1 : List, l2 : List) : List = (l1 match {
      case Nil() => l2
      case Cons(x,xs) => Cons(x, append(xs, l2))                  
    }) ensuring(res => true template((a,c) => time <= a*size(l1) + c)) 
    //ensuring(res => size(res) == size(l1) + size(l2))    
    // ensuring(res => true template((a) => time <= 6*size(l1) + 2))
    //ensuring(res => true template((a,b,c) => time <= a*size(l1) + b*size(l2) + c)) 
    //ensuring(res => size(res) != size(l1) - 1)
    //template((a,b,c) => a*size(l1) + b*size(res) <= 0)
}

/*object ListWithSize {
  sealed abstract class List

  case class Cons(head: Int, tail: List) extends List

  case class Nil() extends List

  def size(l: List): Int = {
    l match {
      case Nil() =>
        0
      case Cons(_, t) =>
        1 + size(t)
    }
  } ensuring(r => r >= 0)

  def append(l1: List, l2: List): (List, Int) = {
    l1 match {
      case Nil() => (l2, 1)
      case Cons(x, xs) => {
        val (e2,t3) = {
          val (e4,t5) = {
            val (e6,t7) = {
              val (e9, t10) = append(xs, l2)
              (e9, (1 + (1 + t10)))
            }
            (Cons(x, e6), (t7 + 2))
          }
          (e4, (1 + t5))
        }
        (e2, (1 + t3))
      }
    }
  } ensuring (res => res._2 <= 6 * size(l1) + 2)*/
  
  /*def main(args : Array[String]) = {
    val l1 = Cons(4, Cons(15, Nil()))
    val l2 = Nil()
    val time = append(l1,l2)._2
    val bound = 5*size(l1) + 2
    println("Time: "+time+" bound: "+bound)
  }*/
//}
