import leon.lang._
import leon.collection._
import leon.annotation._
import leon.lang.synthesis._
 
object StringTest {
  
  def listToString(in : List[String]): String =  {
    ???[String]
  } ensuring {
    (res : String) => (in, res) passes {
      case s if s == List("1", "2", "0") =>
        "[1 ## 2 ## 0]"
      case s if s == List[String]() =>
        "[]"
    }
  }
  
  def setToString(in : Set[String]): String =  {
    ???[String]
  } ensuring {
    (res : String) => (in, res) passes {
      case s if s == Set[String]("1", "2", "0") =>
        "{0 | 1 | 2}"
      case s if s == Set[String]() =>
        "{}"
    }
  }
  
  def mapToString(in : Map[String, String]): String =  {
    ???[String]
  } ensuring {
    (res : String) => (in, res) passes {
      case s if s == Map[String,String]("Title" -> "Modular Printing", "Abstract" -> "We discuss...", "Year" -> "2016") =>
        "[Abstract --> We discuss..., Title --> Modular Printing, Year --> 2016]"
      case s if s == Map[String,String]() =>
        "[]"
    }
  }
  
  def bagToString(in : Bag[String]): String =  {
    ???[String]
  } ensuring {
    (res : String) => (in, res) passes {
      case s if s == Bag[String]("3" -> BigInt(2), "2" -> BigInt(1), "5" -> BigInt(3)) =>
        "2*3*3*5*5*5"
      case s if s == Bag[String]() =>
        ""
    }
  }
}
