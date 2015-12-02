import leon.lang._
import leon.annotation._
import leon.collection._
import leon.collection.ListOps._
import leon.lang.synthesis._

object ListsToString {

  def allListsAreEmpty(t: List[Int]): Boolean = (t.isEmpty || t.tail.isEmpty || t.tail.tail.isEmpty || t.tail.head == 0) holds
  
  def listToString(p : List[Int]): String =  {
    ???
  } ensuring {
    (res : String) => (p, res) passes {
      case Cons(1, Cons(2, Nil())) =>
        "[1, 2]"
    }
  }
}
