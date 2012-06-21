import leon.Utils._

object Epsilon4 {

  sealed abstract class MyList
  case class MyCons(head: Int, tail: MyList) extends MyList
  case class MyNil() extends MyList

  def size(lst: MyList): Int = (lst match {
    case MyNil() => 0
    case MyCons(_, xs) => 1 + size(xs)
  })

  def toSet(lst: MyList): Set[Int] = lst match {
    case MyCons(x, xs) => toSet(xs) ++ Set(x)
    case MyNil() => Set[Int]()
  }

  def toList(set: Set[Int]): MyList = if(set == Set.empty[Int]) MyNil() else {
    val elem = epsilon((x : Int) => set contains x)
    MyCons(elem, toList(set -- Set[Int](elem)))
  }

  def sizeToListEq(lst: MyList): Boolean = (size(toList(toSet(lst))) == size(lst)) holds

  def sizeToListLessEq(lst: MyList): Boolean = (size(toList(toSet(lst))) <= size(lst)) holds

  def toListEq(lst: MyList): Boolean = (toList(toSet(lst)) == lst) holds

  def positiveNum(): Int = epsilon((x: Int) => x > 0) ensuring(_ > 0)


  def linearEquation(): (Int, Int) = {
    val sol = epsilon((t: (Int, Int)) => 2*t._1 + 3*t._2 == 10 && t._1 >= 0 && t._2 >= 0)
    sol
  } ensuring(res => res == (2, 2) || res == (5, 0))


  def nonDeterminsticExecution(): Int = {
    var i = 0
    var b = epsilon((x: Boolean) => i == i)
    while(b) {
      i = i + 1
      b = epsilon((x: Boolean) => i == i)
    }
    i
  } ensuring(_ <= 10)
  

}
