import leon.lang._
import leon.collection._
import leon.lang.synthesis._

object Diffs {

  def diffs(l: List[BigInt]): List[BigInt] = 
    choose((res: List[BigInt]) => 
      res.size == l.size && undiff(res) == l
    )

  def undiff(l: List[BigInt]) = {
    l.scanLeft(BigInt(0))(_ + _).tail
  }
} 

