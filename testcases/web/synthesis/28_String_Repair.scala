import leon.lang._
import leon.collection._

object StringRepair {
  // Two changes needed
  def test(a : List[String]): String =  {
    "(" + List.mkString[String](a, ", ", (s : String) => s) + ")"
  } ensuring {
    (res : String) => (a, res) passes {
      case Cons("A", Nil()) =>
        "[A]"
    }
  }
  
  // One change needed on a recursive function
  def unary(a: BigInt): String= {
    if(a <= 0) ""
    else "i" + unary(a-1)
  } ensuring {
    (res: String) => (a, res) passes {
      case a if a == BigInt(3) => "kkk"
    }
  }
  
  // Two changes needed on one recursive function
  def boundaries(a: List[BigInt]): String= {
    def boundariesrec(a: BigInt): String = {
      if(a <= 0) ";"
      else "=" + boundariesrec(a-1)
    }
    List.mkString[BigInt](a, " ", boundariesrec)
  } ensuring {
    (res: String) => (a, res) passes {
      case a if a == List(BigInt(1), BigInt(2)) => "=|=="
    }
  }
  
  // Three changes requiring clarification.
  def boundaries2(a: List[BigInt]): String= {
    def boundaries2rec(a: BigInt): String = {
      if(a <= 0) ";"
      else "i" + boundaries2rec(a-1)
    }
    List.mkString[BigInt](a, " ", boundaries2rec)
  } ensuring {
    (res: String) => (a, res) passes {
      case a if a == List(BigInt(1), BigInt(2)) => "=|=="
    }
  }
}