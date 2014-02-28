import leon.lang._

object Epsilon4 {

  sealed abstract class MyList
  case class MyCons(head: Int, tail: MyList) extends MyList
  case class MyNil() extends MyList

  def size(lst: MyList): Int = lst match {
    case MyNil() => 0
    case MyCons(_, xs) => 1 + size(xs)
  }

  def setSize(set: Set[Int]): Int = {
    if(set == Set.empty[Int]) 
      0 
    else {
     val elem = epsilon((x : Int) => set contains x)
     1 + setSize(set -- Set[Int](elem))
    }
  } ensuring(_ >= 0)


  def toSet(lst: MyList): Set[Int] = lst match {
    case MyCons(x, xs) => toSet(xs) ++ Set(x)
    case MyNil() => Set[Int]()
  }

  def toList(set: Set[Int]): MyList = {
    if(set == Set.empty[Int]) 
      MyNil() 
    else {
     val elem = epsilon((x : Int) => set contains x)
     MyCons(elem, toList(set -- Set[Int](elem)))
    }
  }

  def sizeToListEq(lst: MyList): Boolean = {
    size(toList(toSet(lst))) == size(lst)
  } holds

  //cannot prove
  //def sizeToListLessEq(lst: MyList): Boolean = {
  //  size(toList(toSet(lst))) <= size(lst)
  //} holds

  def toListEq(lst: MyList): Boolean = {
    toList(toSet(lst)) == lst
  } holds

  def positiveNum(): Int = {
    epsilon((x: Int) => x > 0) 
  } ensuring(_ > 0)

  def negativeNum(): Int = {
    epsilon((x: Int) => x < 0) 
  } ensuring(_ < 0)

  def linearEquation(): (Int, Int) = {
    val sol = epsilon((t: (Int, Int)) => 
      2*t._1 + 3*t._2 == 10 && t._1 >= 0 && t._2 >= 0)
    sol
  } ensuring(res => res == (2, 2) || res == (5, 0))


  def nonDeterministicExecution(): Int = {
    var i = 0
    var b = epsilon((x: Boolean) => true)
    while(b) {
      i = i + 1
      b = epsilon((x: Boolean) => true)
    }
    i
  } ensuring(_ <= 10)
  

}
