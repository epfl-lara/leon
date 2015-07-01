import leon.annotation._
import leon.lang._
import leon.collection._

object FiniteDistributions {

  /*
   * number of outcomes for each index (ps(0) outcomes of value 0, ps(1) outcomes of value 1).
   * Sort of generalization of a dice distribution
   */
  //case class FiniteDist(ps: List[BigInt])

  case class FiniteDist(domain: List[BigInt], outcomes: Map[BigInt, BigInt])

  def isUniform(dist: FiniteDist): Boolean = dist.domain match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, rest@Cons(y, _)) => outcomes(x) == outcomes(y) && isUniform(FiniteDist(rest, dist.domain))
  }

  def isDist(dist: FiniteDist): Boolean = {
    
    def allPos(dist: FiniteDist): Boolean = dist.ps match {
      case Cons(x, Nil()) => x >= 0
      case Cons(x, xs) => x >= 0 && isDist(xs)
    }
    def atLeastOne(dist: FiniteDist): Boolean = dist.ps match {
      case Cons(x, xs) => x > 0 || atLeastOne(xs)
      case Nil => false
    }

    allPos(dist) && atLeastOne(dist)
  }

  def probaHead(dist1: FiniteDist, dist2: FiniteDist): BigInt = {
    require(isDist(dist1) && isDist(dist2) && dist1.size == dist2.size)
    if(dist1.ps.isEmpty) 0 else dist1.head*dist2.last + probaHead(dist1.tail, dist2.init)
  }

  def sumMod(dist1: FiniteDist, dist2: FiniteDist): FiniteDist = {
    require(isDist(dist1) && isDist(dist2) && dist1.size == dist2.size)

    def 
    rotate(1)
  }

  def uniformSumProperties1(dice1: DiceDist, dice2: DiceDist): Boolean = {
    require(isDist(dice1) && isDist(dice2) && isUniform(dice1) && isUniform(dice2))
    val dist = sum(dice1, dice2)

    dist.p2 == dist.p12 &&
    dist.p3 == dist.p11 &&
    dist.p4 == dist.p10 &&
    dist.p5 == dist.p9 &&
    dist.p6 == dist.p8
  } holds
  
  def uniformSumMostLikelyOutcome(dice1: DiceDist, dice2: DiceDist): Boolean = {
    require(isDist(dice1) && isDist(dice2) && isUniform(dice1) && isUniform(dice2))
    val dist = sum(dice1, dice2)
    
    dist.p7 >  dist.p1  && dist.p7 > dist.p2  && dist.p7 > dist.p3  &&
    dist.p7 >  dist.p4  && dist.p7 > dist.p5  && dist.p7 > dist.p6  &&
    dist.p7 >= dist.p7  && dist.p7 > dist.p8  && dist.p7 > dist.p9  &&
    dist.p7 >  dist.p10 && dist.p7 > dist.p11 && dist.p7 > dist.p12
  } holds

  def sumModIsUniform1(dice1: DiceDist, dice2: DiceDist): Boolean = {
    require(isDist(dice1) && isDist(dice2) && isUniform(dice1) && isUniform(dice2))
    val dist = sumMod(dice1, dice2)
    isUniform(dist)
  } holds

  def sumModIsUniform2(dice1: DiceDist, dice2: DiceDist): Boolean = {
    require(isDist(dice1) && isDist(dice2) && isUniform(dice1))
    val dist = sumMod(dice1, dice2)
    isUniform(dist)
  } holds
}
