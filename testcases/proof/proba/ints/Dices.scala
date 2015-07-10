import leon.annotation._
import leon.lang._

object Dices {

  /*
   * number of outcomes for each face of a dice
   */
  case class DiceDist(p1: BigInt, p2: BigInt, p3: BigInt, p4: BigInt, p5: BigInt, p6: BigInt)

  case class SumDist(p1: BigInt, p2: BigInt, p3: BigInt, p4:  BigInt, p5:  BigInt, p6:  BigInt,
                     p7: BigInt, p8: BigInt, p9: BigInt, p10: BigInt, p11: BigInt, p12: BigInt)

  def isUniform(dist: DiceDist): Boolean = dist.p1 == dist.p2 && dist.p2 == dist.p3 && dist.p3 == dist.p4 &&
                                           dist.p4 == dist.p5 && dist.p5 == dist.p6

  def isDist(dice: DiceDist): Boolean = 
    dice.p1 >= 0 && dice.p2 >= 0 && dice.p3 >= 0 && dice.p4 >= 0 && dice.p5 >= 0 && dice.p6 >= 0 &&
    (dice.p1 > 0 || dice.p2 > 0 || dice.p3 > 0 || dice.p4 > 0 || dice.p5 > 0 || dice.p6 > 0)

  def sum(dice1: DiceDist, dice2: DiceDist): SumDist = {
    require(isDist(dice1) && isDist(dice2))
    SumDist(0,                                                                              //1
            dice1.p1*dice2.p1,                                                              //2
            dice1.p1*dice2.p2 + dice1.p2*dice2.p1,                                          //3
            dice1.p1*dice2.p3 + dice1.p2*dice2.p2 + dice1.p3*dice2.p1,                      //4
            dice1.p1*dice2.p4 + dice1.p2*dice2.p3 + dice1.p3*dice2.p2 + dice1.p4*dice2.p1,  //5
            dice1.p1*dice2.p5 + dice1.p2*dice2.p4 + dice1.p3*dice2.p3 + 
            dice1.p4*dice2.p2 + dice1.p5*dice2.p1,                                          //6
            dice1.p1*dice2.p6 + dice1.p2*dice2.p5 + dice1.p3*dice2.p4 + 
            dice1.p4*dice2.p3 + dice1.p5*dice2.p2 + dice1.p6*dice2.p1,                      //7
            dice1.p2*dice2.p6 + dice1.p3*dice2.p5 + dice1.p4*dice2.p4 + 
            dice1.p5*dice2.p3 + dice1.p6*dice2.p2,                                          //8
            dice1.p3*dice2.p6 + dice1.p4*dice2.p5 + dice1.p5*dice2.p4 + dice1.p6*dice2.p3,  //9
            dice1.p4*dice2.p6 + dice1.p5*dice2.p5 + dice1.p6*dice2.p4,                      //10
            dice1.p5*dice2.p6 + dice1.p6*dice2.p5,                                          //11
            dice1.p6*dice2.p6                                                               //12
    )
  }

  //distribution of the addition modulo 6 of two dices
  def sumMod(dice1: DiceDist, dice2: DiceDist): DiceDist = {
    require(isDist(dice1) && isDist(dice2))
    DiceDist(
      dice1.p1*dice2.p6 + dice1.p2*dice2.p5 + dice1.p3*dice2.p4 + dice1.p4*dice2.p3 + dice1.p5*dice2.p2 + dice1.p6*dice2.p1, //1
      dice1.p1*dice2.p1 + dice1.p2*dice2.p6 + dice1.p3*dice2.p5 + dice1.p4*dice2.p4 + dice1.p5*dice2.p3 + dice1.p6*dice2.p2, //2
      dice1.p1*dice2.p2 + dice1.p2*dice2.p1 + dice1.p3*dice2.p6 + dice1.p4*dice2.p5 + dice1.p5*dice2.p4 + dice1.p6*dice2.p3, //3
      dice1.p1*dice2.p3 + dice1.p2*dice2.p2 + dice1.p3*dice2.p1 + dice1.p4*dice2.p6 + dice1.p5*dice2.p5 + dice1.p6*dice2.p4, //4
      dice1.p1*dice2.p4 + dice1.p2*dice2.p3 + dice1.p3*dice2.p2 + dice1.p4*dice2.p1 + dice1.p5*dice2.p6 + dice1.p6*dice2.p5, //5
      dice1.p1*dice2.p5 + dice1.p2*dice2.p4 + dice1.p3*dice2.p3 + dice1.p4*dice2.p2 + dice1.p5*dice2.p1 + dice1.p6*dice2.p6  //6
    )
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

  //sum of two non-uniform dices is potentially uniform (no result)
  def sumModNonUniform(dice1: DiceDist, dice2: DiceDist): Boolean = {
    require(isDist(dice1) && isDist(dice2) && !isUniform(dice1) && !isUniform(dice2))
    val dist = sumMod(dice1, dice2)
    !isUniform(dist)
  } holds

}
