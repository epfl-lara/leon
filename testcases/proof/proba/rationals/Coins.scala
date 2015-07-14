import leon.annotation._
import leon.lang._

object Coins {

  case class CoinDist(pHead: Rational) {
    def pTail: Rational = Rational(1) - pHead
  }

  def isDist(dist: CoinDist): Boolean = 
    dist.pHead.isRational && dist.pHead >= Rational(0) && dist.pHead <= Rational(1)


  case class CoinsJoinDist(hh: Rational, ht: Rational, th: Rational, tt: Rational)

  def isDist(dist: CoinsJoinDist): Boolean =
    dist.hh.isRational && dist.hh >= Rational(0) && dist.hh <= Rational(1) &&
    dist.ht.isRational && dist.ht >= Rational(0) && dist.ht <= Rational(1) &&
    dist.th.isRational && dist.th >= Rational(0) && dist.th <= Rational(1) &&
    dist.tt.isRational && dist.tt >= Rational(0) && dist.tt <= Rational(1) &&
    (dist.hh + dist.ht + dist.th + dist.tt) ~ Rational(1)


  def isUniform(dist: CoinDist): Boolean = {
    require(isDist(dist))
    dist.pHead ~ Rational(1, 2)
  }


  def join(c1: CoinDist, c2: CoinDist): CoinsJoinDist =
    CoinsJoinDist(
      c1.pHead*c2.pHead,
      c1.pHead*c2.pTail,
      c1.pTail*c2.pHead,
      c1.pTail*c2.pTail)

  def firstCoin(dist: CoinsJoinDist): CoinDist = {
    require(isDist(dist))
    CoinDist(dist.hh + dist.ht)
  } ensuring(res => res.pTail ~ (dist.th + dist.tt))

  def secondCoin(dist: CoinsJoinDist): CoinDist = {
    require(isDist(dist))
    CoinDist(dist.hh + dist.th)
  } ensuring(res => res.pTail ~ (dist.ht + dist.tt))

  def isIndependent(dist: CoinsJoinDist): Boolean = {
    require(isDist(dist))
    join(firstCoin(dist), secondCoin(dist)) == dist
  }

  def isEquivalent(dist1: CoinsJoinDist, dist2: CoinsJoinDist): Boolean = {
    require(isDist(dist1) && isDist(dist2))

    (dist1.hh ~ dist2.hh) &&
    (dist1.ht ~ dist2.ht) &&
    (dist1.th ~ dist2.th) &&
    (dist1.tt ~ dist2.tt)
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
  } ensuring(res => res.pTail ~ (coin1.pHead*coin2.pTail + coin1.pTail*coin2.pHead))

  def sum(dist: CoinsJoinDist): CoinDist = {
    require(isDist(dist))
    CoinDist(dist.hh + dist.tt)
  } ensuring(res => res.pTail ~ (dist.ht + dist.th))




  /***************************************************
   *          properties of sum operation            *
   ***************************************************/

  //def sumIsUniform1(coin1: CoinDist, coin2: CoinDist): Boolean = {
  //  require(isDist(coin1) && isDist(coin2) && isUniform(coin1) && isUniform(coin2))
  //  val dist = sum(coin1, coin2)
  //  isUniform(dist)
  //} holds

  //def sumIsUniform2(coin1: CoinDist, coin2: CoinDist): Boolean = {
  //  require(isDist(coin1) && isDist(coin2) && isUniform(coin1))
  //  val dist = sum(coin1, coin2)
  //  isUniform(dist)
  //} holds

  //def sumUniform3(coin1: CoinDist, coin2: CoinDist, coin3: CoinDist): Boolean = {
  //  require(isDist(coin1) && isDist(coin2) && isDist(coin3) && isUniform(coin1))
  //  val dist = sum(sum(coin1, coin2), coin3)
  //  isUniform(dist)
  //} holds

  //def sumUniformWithIndependence(dist: CoinsJoinDist): Boolean = {
  //  require(isDist(dist) && isIndependent(dist) && (isUniform(firstCoin(dist)) || isUniform(secondCoin(dist))))
  //  val res = sum(dist)
  //  isUniform(res)
  //} holds

  ////should find counterexample, indepenence is required
  //def sumUniformWithoutIndependence(dist: CoinsJoinDist): Boolean = {
  //  require(isDist(dist) && (isUniform(firstCoin(dist)) || isUniform(secondCoin(dist))))
  //  val res = sum(dist)
  //  isUniform(res)
  //} holds


  ////sum of two non-uniform dices is potentially uniform (no result)
  //def sumNonUniform1(coin1: CoinDist, coin2: CoinDist): Boolean = {
  //  require(isDist(coin1) && isDist(coin2) && !isUniform(coin1) && !isUniform(coin2))
  //  val dist = sum(coin1, coin2)
  //  !isUniform(dist)
  //} holds

  //def sumNonUniform2(coin1: CoinDist, coin2: CoinDist, coin3: CoinDist): Boolean = {
  //  require(isDist(coin1) && isDist(coin2) && isDist(coin3) && !isUniform(coin1) && !isUniform(coin2) && !isUniform(coin3))
  //  val dist = sum(sum(coin1, coin2), coin3)
  //  !isUniform(dist)
  //} //holds

  //def sumNonUniformWithIndependence(dist: CoinsJoinDist): Boolean = {
  //  require(isDist(dist) && isIndependent(dist) && !isUniform(firstCoin(dist)) && !isUniform(secondCoin(dist)))
  //  val res = sum(dist)
  //  !isUniform(res)
  //} holds

  ////independence is required
  //def sumNonUniformWithoutIndependence(dist: CoinsJoinDist): Boolean = {
  //  require(isDist(dist) && !isUniform(firstCoin(dist)) && !isUniform(secondCoin(dist)))
  //  val res = sum(dist)
  //  !isUniform(res)
  //} holds


  //def sumIsCommutative(coin1: CoinDist, coin2: CoinDist, coin3: CoinDist): Boolean = {
  //  require(isDist(coin1) && isDist(coin2))
  //  sum(coin1, coin2) == sum(coin2, coin1)
  //} holds

  //def sumIsAssociative(coin1: CoinDist, coin2: CoinDist, coin3: CoinDist): Boolean = {
  //  require(isDist(coin1) && isDist(coin2) && isDist(coin3))
  //  sum(sum(coin1, coin2), coin3) == sum(coin1, sum(coin2, coin3))
  //} //holds

}
