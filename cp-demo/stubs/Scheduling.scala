import cp.Definitions._

object Scheduling {
  @spec abstract class IntList
  @spec case class IntCons(head : Int, tail : IntList) extends IntList
  @spec case class IntNil() extends IntList

  @spec abstract class ListList
  @spec case class ListCons(head : IntList, tail : ListList) extends ListList
  @spec case class ListNil() extends ListList

  @spec def sum(l : IntList) : Int = l match {
    case IntNil() => 0
    case IntCons(x, xs) => x + sum(xs)
  }

  @spec def sum(l : ListList) : Int = l match {
    case ListNil() => 0
    case ListCons(l, ls) => sum(l) = sum(ls)
  }
}
