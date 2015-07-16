import leon.annotation._
import leon.lang._

object Coins {

  case class CoinDist(pHead: Real) {
    def pTail: Real = {
      require(pHead >= Real(0) && pHead <= Real(1))
      Real(1) - pHead
    } ensuring(res => res >= Real(0) && res <= Real(1))
  }

  def isDist(dist: CoinDist): Boolean = 
    dist.pHead >= Real(0) && dist.pHead <= Real(1)


  case class CoinsJoinDist(hh: Real, ht: Real, th: Real, tt: Real)

  def isDist(dist: CoinsJoinDist): Boolean =
    dist.hh >= Real(0) && dist.hh <= Real(1) &&
    dist.ht >= Real(0) && dist.ht <= Real(1) &&
    dist.th >= Real(0) && dist.th <= Real(1) &&
    dist.tt >= Real(0) && dist.tt <= Real(1) &&
    (dist.hh + dist.ht + dist.th + dist.tt) == Real(1)


  def isUniform(dist: CoinDist): Boolean = {
    require(isDist(dist))
    dist.pHead == Real(1, 2)
  }


  def join(c1: CoinDist, c2: CoinDist): CoinsJoinDist = {
    //require(isDist(c1) && isDist(c2))
    require(
      c1.pHead >= Real(0) && c1.pHead <= Real(1) &&
      c2.pHead >= Real(0) && c2.pHead <= Real(1)
    )

    CoinsJoinDist(
      c1.pHead*c2.pHead,
      c1.pHead*(Real(1)-c2.pHead),
      (Real(1)-c1.pHead)*c2.pHead,
      (Real(1)-c1.pHead)*(Real(1)-c2.pHead)
    )
  } ensuring(res =>
      res.hh >= Real(0) && res.hh <= Real(1) &&
      res.ht >= Real(0) && res.ht <= Real(1) &&
      res.th >= Real(0) && res.th <= Real(1) &&
      res.tt >= Real(0) && res.tt <= Real(1) &&
      (res.hh + res.ht + res.th + res.tt) == Real(1)
    )

  def firstCoin(dist: CoinsJoinDist): CoinDist = {
    require(isDist(dist))
    CoinDist(dist.hh + dist.ht)
  } ensuring(res => isDist(res) && res.pTail == (dist.th + dist.tt))

  def secondCoin(dist: CoinsJoinDist): CoinDist = {
    require(isDist(dist))
    CoinDist(dist.hh + dist.th)
  } ensuring(res => isDist(res) && res.pTail == (dist.ht + dist.tt))

  def isIndependent(dist: CoinsJoinDist): Boolean = {
    require(isDist(dist))
    join(firstCoin(dist), secondCoin(dist)) == dist
  }

  def isEquivalent(dist1: CoinsJoinDist, dist2: CoinsJoinDist): Boolean = {
    require(isDist(dist1) && isDist(dist2))

    (dist1.hh == dist2.hh) &&
    (dist1.ht == dist2.ht) &&
    (dist1.th == dist2.th) &&
    (dist1.tt == dist2.tt)
  }


  //case class CoinCondDist(ifHead: CoinDist, ifTail: CoinDist)

  //def condByFirstCoin(dist: CoinsJoinDist): CoinCondDist = {
  //  CoinCondDist(
  //    CoinDist(
  //      dist.hh*(dist.th + dist.tt), //probability of head if head
  //      dist.ht*(dist.th + dist.tt)  //probability of tail if head
  //    ),
  //    CoinDist(
  //      dist.th*(dist.hh + dist.ht), //probability of head if tail
  //      dist.tt*(dist.hh + dist.ht)  //probability of tail if tail
  //    )
  //  )
  //}

  //def combine(cond: CoinCondDist, dist: CoinDist): CoinsJoinDist = {
  //  require(isDist(dist) && dist.pHead > 0 && dist.pTail > 0)

  //  val hh = cond.ifHead.pHead * dist.pHead
  //  val ht = cond.ifHead.pTail * dist.pHead
  //  val th = cond.ifTail.pHead * dist.pTail
  //  val tt = cond.ifTail.pTail * dist.pTail
  //  CoinsJoinDist(hh, ht, th, tt)
  //}
  //
  //def condIsSound(dist: CoinsJoinDist): Boolean = {
  //  require(isDist(dist) && dist.hh > 0 && dist.ht > 0 && dist.th > 0 && dist.tt > 0)

  //  val computedDist = combine(condByFirstCoin(dist), firstCoin(dist))
  //  isEquivalent(dist, computedDist)
  //} holds


  //should be INVALID
  def anyDistributionsNotEquivalent(dist1: CoinsJoinDist, dist2: CoinsJoinDist): Boolean = {
    require(isDist(dist1) && isDist(dist2))
    isEquivalent(dist1, dist2)
  } holds

  //sum modulo: face is 0, tail is 1
  def sum(coin1: CoinDist, coin2: CoinDist): CoinDist = {
    require(isDist(coin1) && isDist(coin2))
    CoinDist(coin1.pHead*coin2.pHead + coin1.pTail*coin2.pTail)
  } ensuring(res => isDist(res) && res.pTail == (coin1.pHead*coin2.pTail + coin1.pTail*coin2.pHead))

  def sum(dist: CoinsJoinDist): CoinDist = {
    require(isDist(dist))
    CoinDist(dist.hh + dist.tt)
  } ensuring(res => isDist(res) && res.pTail == (dist.ht + dist.th))




  /***************************************************
   *          properties of sum operation            *
   ***************************************************/

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

  def sumUniform3(coin1: CoinDist, coin2: CoinDist, coin3: CoinDist): Boolean = {
    require(isDist(coin1) && isDist(coin2) && isDist(coin3) && isUniform(coin1))
    val dist = sum(sum(coin1, coin2), coin3)
    isUniform(dist)
  } holds

  def sumUniformWithIndependence(dist: CoinsJoinDist): Boolean = {
    require(isDist(dist) && isIndependent(dist) && (isUniform(firstCoin(dist)) || isUniform(secondCoin(dist))))
    val res = sum(dist)
    isUniform(res)
  } holds

  //should find counterexample, indepenence is required
  def sumUniformWithoutIndependence(dist: CoinsJoinDist): Boolean = {
    require(isDist(dist) && (isUniform(firstCoin(dist)) || isUniform(secondCoin(dist))))
    val res = sum(dist)
    isUniform(res)
  } holds


  ////sum of two non-uniform dices is potentially uniform (no result)
  def sumNonUniform1(coin1: CoinDist, coin2: CoinDist): Boolean = {
    require(isDist(coin1) && isDist(coin2) && !isUniform(coin1) && !isUniform(coin2))
    val dist = sum(coin1, coin2)
    !isUniform(dist)
  } holds

  def sumNonUniform2(coin1: CoinDist, coin2: CoinDist, coin3: CoinDist): Boolean = {
    require(isDist(coin1) && isDist(coin2) && isDist(coin3) && !isUniform(coin1) && !isUniform(coin2) && !isUniform(coin3))
    val dist = sum(sum(coin1, coin2), coin3)
    !isUniform(dist)
  } holds

  def sumNonUniformWithIndependence(dist: CoinsJoinDist): Boolean = {
    require(isDist(dist) && isIndependent(dist) && !isUniform(firstCoin(dist)) && !isUniform(secondCoin(dist)))
    val res = sum(dist)
    !isUniform(res)
  } holds

  //independence is required
  def sumNonUniformWithoutIndependence(dist: CoinsJoinDist): Boolean = {
    require(isDist(dist) && !isUniform(firstCoin(dist)) && !isUniform(secondCoin(dist)))
    val res = sum(dist)
    !isUniform(res)
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
