package NewViterbi

import leon.collection._
import leon._
import leon.mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import leon.collection._

object Viterbi {
  @extern
  def Otime(i : BigInt): (BigInt, BigInt) = ((0, 1) : (BigInt, BigInt))
  
  @extern
  def Stime(i : BigInt): (BigInt, BigInt) = ((0, 1) : (BigInt, BigInt))
  
  @extern
  def Atime(i : BigInt, j : BigInt): (BigInt, BigInt) = ((0, 1) : (BigInt, BigInt))
  
  @extern
  def Btime(i : BigInt, j : BigInt): (BigInt, BigInt) = ((0, 1) : (BigInt, BigInt))
  
  @extern
  def Ctime(i : BigInt): (BigInt, BigInt) = ((0, 1) : (BigInt, BigInt))
  
  @extern
  def Ytime(i : BigInt): (BigInt, BigInt) = ((0, 1) : (BigInt, BigInt))
  
  @invstate
  def fillEntrytime(l : BigInt, i : BigInt, j : BigInt, K : BigInt): (BigInt, BigInt) = {
    val e125 = j - BigInt(1)
    val lr = lookup[BigInt](List(4934, l, e125, K))
    val e36 = if (lr._1) {
      (lr._2, BigInt(2))
    } else {
      val e35 = viterbitime(l, e125, K)
      (update[BigInt](List(4934, l, e125, K), e35._1), BigInt(4) + e35._2)
    }
    val e39 = Atime(l, i)
    val e130 = e39._2
    val e44 = Ytime(j)
    val e134 = e44._2
    val e46 = Btime(i, e44._1)
    val e138 = e46._2
    val ir = ((e36._1 + e39._1) + e46._1, (((BigInt(2) + e138) + e134) + e130) + e36._2)
    val r159 = if (l == K) {
      (ir._1, BigInt(2))
    } else {
      val e54 = fillEntrytime(BigInt(1) + l, i, j, K)
      val e143 = e54._1
      val c10 = (ir._1 > e143, BigInt(1))
      val r158 = if (ir._1 > e143) {
        (ir._1, BigInt(1) + c10._2)
      } else {
        (e143, BigInt(1) + c10._2)
      }
      (r158._1, (BigInt(4) + r158._2) + e54._2)
    }
    (r159._1, ((((BigInt(2) + r159._2) + e138) + e134) + e130) + e36._2)
  }
  
  @invstate
  @memoize
  def viterbitime(i : BigInt, j : BigInt, K : BigInt): (BigInt, BigInt) = {
    val bd = if (j == BigInt(0)) {
      val e15 = Ctime(i)
      val e19 = Ytime(BigInt(0))
      val e21 = Btime(i, e19._1)
      (e15._1 + e21._1, ((BigInt(3) + e21._2) + e19._2) + e15._2)
    } else {
      val e27 = fillEntrytime(BigInt(0), i, j, K)
      (e27._1, BigInt(3) + e27._2)
    }
    (bd._1, bd._2)
  }
  
  def invoketime(i : BigInt, j : BigInt, K : BigInt): (BigInt, BigInt) = {
    val lr1 = lookup[BigInt](List(4934, i, j, K))
    val bd2 = if (lr1._1) {
      (lr1._2, BigInt(1))
    } else {
      val e62 = viterbitime(i, j, K)
      (update[BigInt](List(4934, i, j, K), e62._1), BigInt(3) + e62._2)
    }
    (bd2._1, bd2._2)
  }
  
  def fillColumntime(i : BigInt, j : BigInt, K : BigInt): (List[BigInt], BigInt) = {
    val bd4 = if (i == K) {
      val e70 = invoketime(i, j, K)
      (List[BigInt](e70._1), BigInt(5) + e70._2)
    } else {
      val e76 = invoketime(i, j, K)
      val e82 = fillColumntime(BigInt(1) + i, j, K)
      (Cons[BigInt](e76._1, e82._1), (BigInt(6) + e82._2) + e76._2)
    }
    (bd4._1, bd4._2)
  }
  
  @invisibleBody
  def fillTabletime(j : BigInt, T : BigInt, K : BigInt): (List[List[BigInt]], BigInt) = {
    val bd5 = if (j == T) {
      val e90 = fillColumntime(BigInt(0), j, K)
      (List[List[BigInt]](e90._1), BigInt(5) + e90._2)
    } else {
      val e96 = fillColumntime(BigInt(0), j, K)
      val e102 = fillTabletime(BigInt(1) + j, T, K)
      (Cons[List[BigInt]](e96._1, e102._1), (BigInt(6) + e102._2) + e96._2)
    }
    (bd5._1, bd5._2)
  }
  
  def viterbiSolstime(T : BigInt, K : BigInt): (List[List[BigInt]], BigInt) = {
    val e66 = fillTabletime(BigInt(0), T, K)
    (e66._1, BigInt(1) + e66._2)
  }
  
}
