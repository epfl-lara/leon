import leon.annotation._
import leon.lang._

object Coins {

  /*
   * number of outcomes for each face
   */
  case class CoinDist(pHead: BigInt, pTail: BigInt)


  def isUniform(dist: CoinDist): Boolean = {
    require(isDist(dist))
    dist.pHead == dist.pTail
  }

  def isDist(dist: CoinDist): Boolean = 
    dist.pHead >= 0 && dist.pTail >= 0 && (dist.pHead > 0 || dist.pTail > 0)

  //sum modulo: face is 0, tail is 1
  def sum(coin1: CoinDist, coin2: CoinDist): CoinDist = {
    require(isDist(coin1) && isDist(coin2))
    CoinDist(
      coin1.pHead*coin2.pHead + coin1.pTail*coin2.pTail,
      coin1.pHead*coin2.pTail + coin1.pTail*coin2.pHead
    )
  }

  def sumIsUniform1(coin1: CoinDist, coin2: CoinDist): Boolean = {
    require(isDist(coin1) && isDist(coin2) && isUniform(coin1) && isUniform(coin2))
    val dist = sum(coin1, coin2)
    isUniform(dist)
  } holds

  def sumIsUniform2(coin1: CoinDist, coin2: CoinDist): Boolean = {
    require(isDist(coin1) && isDist(coin2) && isUniform(coin1))
    val dist = sum(coin1, coin2)
    isUniform(dist)
  } holds

  //sum of two non-uniform dices is potentially uniform (no result)
  def sumNonUniform1(coin1: CoinDist, coin2: CoinDist): Boolean = {
    require(isDist(coin1) && isDist(coin2) && !isUniform(coin1) && !isUniform(coin2))
    val dist = sum(coin1, coin2)
    !isUniform(dist)
  } holds

  def sumNonUniform2(coin1: CoinDist, coin2: CoinDist, coin3: CoinDist): Boolean = {
    require(isDist(coin1) && isDist(coin2) && isDist(coin3) && !isUniform(coin1) && !isUniform(coin2) && !isUniform(coin3))
    val dist = sum(sum(coin1, coin2), coin3)
    !isUniform(dist)
  } //holds


  def sumUniform3(coin1: CoinDist, coin2: CoinDist, coin3: CoinDist): Boolean = {
    require(isDist(coin1) && isDist(coin2) && isDist(coin3) && isUniform(coin1))
    val dist = sum(sum(coin1, coin2), coin3)
    isUniform(dist)
  } holds

  def sumIsCommutative(coin1: CoinDist, coin2: CoinDist, coin3: CoinDist): Boolean = {
    require(isDist(coin1) && isDist(coin2))
    sum(coin1, coin2) == sum(coin2, coin1)
  } holds

  def sumIsAssociative(coin1: CoinDist, coin2: CoinDist, coin3: CoinDist): Boolean = {
    require(isDist(coin1) && isDist(coin2) && isDist(coin3))
    sum(sum(coin1, coin2), coin3) == sum(coin1, sum(coin2, coin3))
  } holds

}
