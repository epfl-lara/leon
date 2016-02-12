import leon.lang._
import leon.annotation._
import leon.collection._
import leon.collection.ListOps._
import leon.lang.synthesis._

object OutOfOrderToString {
  def arguments(i: Int, j: Int): String = {
    ???
  } ensuring { (res: String) => ((i, j), res) passes {
    case (1, 2) => "2, 1"
  } }
  
  def tuple(i: (Int, Int)): String = {
    ???
  } ensuring { (res: String) => (i, res) passes {
    case (1, 2) => "2, 1"
  } }
  
  
  def reverseList(l : List[Int]): String =  {
    ???[String]
  } ensuring {
    (res : String) => (l, res) passes {
      case Cons(1, Cons(2, Nil())) =>
        "2, 1"
    }
  }
  
  def listPair(l : List[(Int, Int)]): String =  {
    ???[String]
  } ensuring {
    (res : String) => (l, res) passes {
      case Cons((1, 2), Cons((3, 4), Nil())) =>
        "2 -> 1, 4 -> 3"
    }
  }
  
  def reverselistPair(l: List[(Int, Int)]): String = {
    ???
  } ensuring { (res: String) => (l, res) passes {
    case Cons((1, 2), Cons((3,4), Nil())) => "4 -> 3, 2 -> 1"
  } }
  
  case class Rule(input: Int, applied: Option[Int])
  
  def rule(r : Rule): String =  {
    ???
  } ensuring {
    (res : String) => (r, res) passes {
      case Rule(1, None()) =>
        "res: 1"
      case Rule(4, Some(2)) =>
        "Push(2): 4"
    }
  }
}