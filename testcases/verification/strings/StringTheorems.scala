/* Author : @MikaelMayer 
 * Created: June 2016   */
import leon.lang._
import leon.annotation._
import leon.proof._
 
object StringTest {
  sealed abstract class Nat
  case class Succ(n: Nat) extends Nat
  case object Zero extends Nat
  
  def fc(n: Nat, a: String, b: String, c: String): String = n match {
    case Succ(n) => a + fc(n, a, b, c) + b
    case Zero => c
  }
  
  // Splits the string at a given index.
  def split(s: String, i: BigInt): (String, String) = {
    require(i >= 0 && i <= s.bigLength)
    (s.bigSubstring(0, i), s.bigSubstring(i))
  } ensuring {
    res => res._1 + res._2 == s && res._1.bigLength == i && res._2.bigLength == s.bigLength - i
  }
  
  // Splits the string at a given index starting from the end
  def splitFromEnd(s: String, i: BigInt): (String, String) = {
    require(i >= 0 && i <= s.bigLength)
    val j = s.bigLength - i
    split(s, j)
  } ensuring {
    res => res._1 + res._2 == s && res._1.bigLength == s.bigLength - i && res._2.bigLength == i
  }
  
  // Computes A + A + ... + A,  n times */
  def power(A: String, n: BigInt): String = {
    require(n >= 0)
    if(n == 0) ""
    else if(n == 1) A
    else A + power(A, n-1)
  }
  
  /** A small lemma on string equality */
  def lemmaSplit(A: String, B: String, C: String): BigInt = {
    require(A+B==C)
    A.bigLength
  } ensuring {
    (i: BigInt) => (A, B) == split(C, i)
  }
  
  /** A + B == C + D and |A| == |C| <==> B == D && A == C */
  def Lemma001EquationSplit(A: String, B: String, C: String, D: String) = {
    require(A + B == C + D && A.bigLength == C.bigLength)
    A == C && B == D
  }.holds
  
  def Lemma002InequalitySplit(p: String, q: String) = {
    p.bigLength < q.bigLength || p.bigLength == q.bigLength || p.bigLength > q.bigLength
  }.holds
  
  // If a string right-commutes with C to yield B on the left, B and C have the same size.
  def Lemma003Stringsizes(A: String, B: String, C: String) = {
    require(A + B == C + A)
    C.bigLength == B.bigLength
  } holds
  
  
  // Associativity
  def LemmaAssociativity(A: String, B: String, C: String): Boolean = {
    (A + B) + C == A + (B + C)
  } holds
  
  // Useful bigger associativity lemma
  def LemmaAssociativity4_1_3(A: String, B: String, C: String, D: String): Boolean = {
    A + (B + C + D) == ((A + B) + C) + D
  } holds
  
  def LemmaAssociativity4_2_3(A: String, B: String, C: String, D: String): Boolean = {
    (A + B + C) + D == (A + B) + (C + D)
  } holds
  
  def LemmaAssociativity4_1_2(A: String, B: String, C: String, D: String): Boolean = {
    (A + B) + (C + D) == A + (B + C + D) 
  } holds
  
  def LemmaAssociativity4_1_2_2(A: String, B: String, C: String, D: String): Boolean = {
    (A + B) + (C + D) == A + (B + C) + D
  } holds
  
  // Useful bigger associativity lemma
  def LemmaAssociativity5_1_2(A: String, B: String, C: String, D: String, E: String): Boolean = {
    A + (B + C + D + E) == (A + B) + (C + D + E)
  } holds
  
  def LemmaAssociativity5_2_3__1_2_2(A: String, B: String, C: String, D: String, E: String): Boolean = {
    (A+B)+(C+D+E) == A+(B+C)+(D+E)
  } holds
  
  // Left simplification
  def LemmaLeftSimplification(A: String, B: String, C: String): Boolean = {
    require(A + B == A + C)
    B == C
  } holds
  
  // Right simplification
  def LemmaRightSimplification(A: String, B: String, C: String): Boolean = {
    require(A + C == B + C)
    A == B
  } holds
  
  
  // Left size simplification
  def LemmaLeftSizeSimplification(A: String, B: String, C: String, D: String): Boolean = {
    require(A.bigLength == C.bigLength && A+B==C+D)
    A == C && B == D
  } holds
  
  // Right size simplification A+B == C+D && |B| == |D| ==> B == D && A == C
  def LemmaRightSizeSimplification(A: String, B: String, C: String, D: String): Boolean = {
    require(B.bigLength == D.bigLength && A+B==C+D)
    A == C && B == D
  } holds
  
  /** |A+B| == |A|+|B|*/
  def LemmaLength(A: String, B: String): Boolean = {
    (A + B).bigLength == A.bigLength + B.bigLength
  } holds
  
  /** Proof that empty to the power of anything is empty */
  def LemmaPowerEmpty(n: BigInt): Boolean = {
    require(n >= 0)
    (if( n == 0) power("", n) == ""
    else
      power("", n) == "" + power("", n-1) &&
      "" + power("", n-1) == power("", n-1) &&
      LemmaPowerEmpty(n-1) &&
      power("", n-1) == "") &&
    power("", n) == ""
  } holds
  
  /** Power can also be defined on the right */
  def LemmaPowerRight(A: String, n: BigInt): Boolean = {
    require(n > 0)
    (if(n == 1) power(A, n - 1) == "" && "" + A == A
    else {
      LemmaPowerKeepsCommutativity(A, A, n-1) &&
      power(A, n - 1) + A == A + power(A, n - 1) &&
      A + power(A, n - 1) == power(A, n)
    }) &&
    power(A, n - 1) + A == power(A, n)
  } holds
  
  def LemmaPowerLeftPlus1(A: String, n: BigInt): Boolean = {
    require(n >= 0)
    A + power(A, n) == power(A, n+1)
  } holds
  
  def LemmaPowerDistributivity(A: String, n: BigInt, m: BigInt): Boolean = {
    require(n >= 0 && m >= 0)
    if(n == 0) power(A, 0) == "" && power(A, n) + power(A, m) == power(A, n + m)
    else {
       power(A, n) == A + power(A, n-1) &&
       power(A, n) + power(A, m) == (A + power(A, n-1)) + power(A, m) &&
       LemmaAssociativity(A, power(A, n-1), power(A, m)) &&
       (A + power(A, n-1)) + power(A, m) == A + (power(A, n-1) + power(A, m)) &&
       LemmaPowerDistributivity(A, n-1, m) &&
       (power(A, n-1) + power(A, m)) == power(A, n-1+m) && 
       LemmaRightEquality(A, power(A, n-1) + power(A, m), power(A, n-1+m)) &&
       A + (power(A, n-1) + power(A, m))  == A + power(A, n-1+m) &&
       A + power(A, n-1+m) == power(A, n-1+m+1) &&
       power(A, n) + power(A, m) == power(A, n + m)
    }
  } ensuring {
    (res: Boolean) => res && power(A, n) + power(A, m) == power(A, n + m)
  }

  /** Returns nm so that power(power(A, n), m) == power(A, nm) */
  def LemmaDoublePower(A: String, n: BigInt, m: BigInt): BigInt = {
    require(n >= 0 && m >= 0)
    if(m == 0) {
      if(LemmaPowerEmpty(m) &&
        power(power(A, n), m) == "" &&
        power(A, 0) == "")
        BigInt(0)
      else error[BigInt]("This should not cause any problem")
    } else {
      if( power(power(A, n), m) == power(A, n) + power(power(A, n), m - 1)) {
        val k = LemmaDoublePower(A, n, m - 1)
        if(power(power(A, n), m-1) == power(A, k) &&
           LemmaRightEquality(power(A, n), power(power(A, n), m - 1), power(A, k)) &&
           power(A, n) + power(power(A, n), m - 1) == power(A, n) + power(A, k) &&
           LemmaPowerDistributivity(A, n, k) &&
           power(A, n) + power(A, k) == power(A, n + k) &&
           power(power(A, n), m) == power(A, n + k)
        )
          n+k
        else error[BigInt]("This should not cause any problem")
      } else error[BigInt]("This should not cause any problem")
    }
  } ensuring {
    (nm: BigInt) => nm >= 0 && power(power(A, n), m) == power(A, nm)
  }
  
  /*3) prefix-introduce
| p |`< | q |  && p A = q B
<=>
There exist a constant k such that q = p k and A = k B*/
  def Lemma005PrefixIntroduce(p: String, A: String, q: String, B: String) = {
    require(p.bigLength < q.bigLength && p + A == q + B)
    val (l, k) = split(q, p.bigLength)
    k
  } ensuring { (k: String) => q == p + k && A == k + B }
  
  /*3bis) suffix-introduce
| p |`< | q |  && A p = B q
<=>
There exist a constant k such that q = k p and A = B k */
  def Lemma006SuffixIntroduce(A: String, p: String, B: String, q: String) = {
    require(p.bigLength < q.bigLength && A + p == B + q)
    val (k, l) = splitFromEnd(q, p.bigLength)
    k
  } ensuring { (k: String) => q == k + p && A == B + k }

  /** If A + B == C + D && |B| < |D| ==> |A| > |C| */
  def LemmaRightGreaterSmaller(A: String, B: String, C: String, D: String) = {
    require(A + B == C + D && B.bigLength < D.bigLength)
    A.bigLength > C.bigLength 
  } holds
  
  /** A + B == B + A ==> there exists t, n, m such that B = nT, A=mT*/
  def LemmaGCD(A: String, B: String): (String, BigInt, BigInt) = {
    require(A + B == B + A)
    if(A.bigLength == B.bigLength) {
      if(LemmaLeftSizeSimplification(A, B, B, A) && A == B) {
        (A, BigInt(1), BigInt(1))
      } else error[(String, BigInt, BigInt)]("This should not happen")
    } else if(A.bigLength < B.bigLength) {
      val (t, na, nb) = LemmaGCD(B, A)
      (t, nb, na)
    } else {
      val k = Lemma005PrefixIntroduce(B, A, A, B)
      if(A == B + k && A == k + B) {
        val (t, nb, nk) = LemmaGCD(B, k)
        (t, nb+nk, nb)
      } else error[(String, BigInt, BigInt)]("This should not happen")
    }
  } ensuring { r => r._2 >= 0 && r._3 >= 0 && A == power(r._1, r._2) && B == power(r._1, r._3) }
  
  def LemmaTripleGCD(A: String, B: String, C: String): (String, BigInt, BigInt, BigInt) = {
    require(A+B+C == C+B+A && A.bigLength < C.bigLength)
    val k = Lemma005PrefixIntroduce(A, B+C, C, B+A)
    if(C == A + k && B+C == k+(B+A) &&
      (A+B)+C == (C+B)+A &&
      LemmaRightEquality(A+B,C,A+k) &&
      (A+B)+C == (A+B)+(A+k) &&
      (A+B)+(A+k) == (C+B)+A &&
      LemmaLeftEquality(C, A+k, B) &&
      C+B == A+k+B &&
      LemmaLeftEquality(C+B, A+k+B, A) &&
      (C+B)+A == ((A + k)+B)+A &&
      (A+B)+(A+k) == ((A + k)+B)+A &&
      LemmaAssociativity(A, B, A+k) &&
      (A+B)+(A+k) == A+(B+(A+k)) &&
      LemmaAssociativity4_1_3(A, k, B, A) &&
      ((A + k)+B)+A == A + (k+B+A) && 
      A+(B+(A+k)) == A + (k+B+A) &&
      LemmaLeftSimplification(A, B+(A+k), k+B+A) &&
      LemmaAssociativity(B, A, k) &&
      B+A+k == k+B+A &&
      LemmaAssociativity(k, B, A) &&
      k+B+A == k + (B+A) &&
      (B+A)+k == k+(B+A)) {
        val (kt, kk, kba) = LemmaGCD(k, B+A)
        if(k == power(kt, kk) && B+A == power(kt, kba)) {
          val mi = lemmaSplit(B, A, power(kt, kba))
          val i = power(kt, kba).bigLength - mi
          if(i >= 0) {
            (kt, i, kba, kk)
          } else error[(String, BigInt, BigInt, BigInt)]("This should not happen")
        }  else error[(String, BigInt, BigInt, BigInt)]("This should not happen")
    } else error[(String, BigInt, BigInt, BigInt)]("This should not happen")
  } ensuring { r =>
     r._2 >= 0 && r._2<= power(r._1, r._3).bigLength && (B, A) == split(power(r._1, r._3), r._2) && C == A + power(r._1, r._4)
  }
  
/*
If A + B == C + A and |A| <= |C|, then there exists k1 and k2 such that
C = k1+k2
B = k2+k1
A = k1
*/
  def LemmaCommutation1(A: String, B: String, C: String) = {
    require(A + B == C + A && C.bigLength >= A.bigLength)
    val (k1, k2) = split(C, A.bigLength)
    (k1, k2)
  } ensuring {
    k => C == k._1 + k._2 && B == k._2 + k._1 && A == k._1
  }
  
/*
  If A + B == C + A and |A| <= |C|, then there exists k1 and k2 such that
  C = k1+k2
  B = k2+k1
  A = k1+k2+k1+..+k2+k1
2)    | C |    Ap      |
1)| C |       A        |
1)|       A        | B |
2)    |    Ap      |
  Hence Ap commutes with C and yields B
*/
  def LemmaPreCondCommutation1(A: String, B: String, C: String): Boolean = {
    require(A + B == C + A && C.bigLength < A.bigLength)
    val (cp, ap) = split(A, C.bigLength)
    cp == C &&
    A == C + ap
  } holds
  
  def LemmaPreCondCommutation2(A: String, B: String, C: String): Boolean = {
    require(A + B == C + A && C.bigLength < A.bigLength)
    val (app, bp) = splitFromEnd(A, B.bigLength)
    bp == B &&
    app + bp == A
  } holds
  
  def LemmaPreCondCommutation(A: String, B: String, C: String): Boolean = {
    require(A + B == C + A && C.bigLength < A.bigLength)
    val (cp, ap) = split(A, C.bigLength)
    val (app, bp) = splitFromEnd(A, B.bigLength)
    LemmaPreCondCommutation1(A, B, C) &&
    LemmaPreCondCommutation2(A, B, C) &&
    C + ap == A &&
    (C + ap) + B == C + A &&
    LemmaAssociativity(C, ap, B) &&
    C + (ap + B) == C + A &&
    LemmaLeftSimplification(C, ap + B, A) &&
    ap + B == A &&
    C + ap == ap + B
  } holds

  /** A + B == C + A ==> C == k1k2 && B == k2k1 */
  def LemmaCommutation2(A: String, B: String, C: String): (String, String, String) = {
    require(A + B == C + A)
    if(C.bigLength >= A.bigLength) {
      val (k1, k2) = LemmaCommutation1(A, B, C)
      (k1, k2, A)
    } else {
      val (c, ap) = split(A, C.bigLength)
      if (LemmaPreCondCommutation(A, B, C)) {
        val k = LemmaCommutation2(ap, B, C)
        (k._1, k._2, k._1 + k._2 + k._3) 
      } else error[(String, String, String)]("Does not happen")
    }
  } ensuring {
    k => C == k._1 + k._2 && B == k._2 + k._1 && A == k._3
  }
  
  /** A + B == C + A ==> C == k1+k2 && B == k2+k1 && A == n(k1+k2)+k1 */
  def LemmaCommutation2Explicit(A: String, B: String, C: String): (String, String, BigInt) = {
    require(A + B == C + A)
    if(C.bigLength >= A.bigLength) {
      val (k1, k2) = LemmaCommutation1(A, B, C)
      (k1, k2, BigInt(0))
    } else {
      val (c, ap) = split(A, C.bigLength)
      if (LemmaPreCondCommutation(A, B, C) && C == c) {
        val k = LemmaCommutation2Explicit(ap, B, C)
        if(C == k._1 + k._2 && B == k._2 + k._1 &&
           ap == power(k._1+k._2,k._3)+k._1 && 
           A == C + ap &&
           C+ap == (k._1 + k._2) + ap &&
           (k._1 + k._2) + ap == (k._1 + k._2) + (power(k._1+k._2,k._3)+k._1) &&
           LemmaAssociativity(k._1+k._2, power(k._1+k._2,k._3), k._1) &&
           (k._1 + k._2) + (power(k._1+k._2,k._3)+k._1) == ((k._1 + k._2) + power(k._1+k._2, k._3))+k._1 &&
           LemmaPowerLeftPlus1(k._1 + k._2, k._3) &&
           (k._1 + k._2) + power(k._1+k._2, k._3) == power(k._1+k._2, k._3 + 1) &&
           LemmaLeftEquality((k._1 + k._2) + power(k._1+k._2, k._3), power(k._1+k._2, k._3 + 1), k._1) &&
           ((k._1 + k._2) + power(k._1+k._2, k._3))+k._1 == (power(k._1+k._2, k._3 + 1))+k._1 &&
           A == (power(k._1+k._2, k._3 + 1))+k._1
           ) {
          (k._1, k._2, k._3 + 1)
        } else error[(String, String, BigInt)]("Does not happen")
      } else error[(String, String, BigInt)]("Does not happen")
    }
  } ensuring {
    k => C == k._1 + k._2 && B == k._2 + k._1 && k._3 >= 0 && A == power(k._1+k._2, k._3)+k._1
  }
  
  def test = LemmaCommutation2Explicit("", "A", "A")
  
  /** A + B == C + A && |C| < |A| ==> C == k1k2 && B == k2k1 && A==k1k2k3 && A == k3k2k1 */
  def LemmaCommutation3(A: String, B: String, C: String): (String, String, String) = {
    require(A + B == C + A && C.bigLength < A.bigLength)
    val (c, ap) = split(A, C.bigLength)
    if (LemmaPreCondCommutation(A, B, C) && c == C && C+ap == A && ap+B == A) {
      val k = LemmaCommutation2(ap, B, C)
      if(k._3 == ap &&
         C == k._1 + k._2 &&
         B == k._2 + k._1 &&
         A == (k._1 + k._2)+k._3 &&
         A == ap + B &&
         A == k._3+(k._2+k._1) && LemmaAssociativity(k._3, k._2, k._1) &&
         A == (k._3+k._2)+k._1
         ) {
        (k._1, k._2, k._3)
      } else error[(String, String, String)]("should not happen")
    } else error[(String, String, String)]("should not happen")
  } ensuring {
    k => C == k._1 + k._2 && B == k._2 + k._1 && A == k._1 + k._2 + k._3 && A == k._3 + (k._2 + k._1) &&
        LemmaAssociativity(k._3, k._2, k._1) && A == k._3 + k._2 + k._1
  }
  
  // Other lemmas
  def LemmaCommutative$0(A: String, B: String, n: BigInt): Boolean = {
    require(n >= 2)
    B + power(A, n) == (B + A) + power(A, n-1)
  } holds
  
  def LemmaCommutative$1(A: String, B: String, n: BigInt): Boolean = {
    require(n >= 2 && A + B == B + A)
    (B + A) + power(A, n-1) == (A + B) + power(A, n-1)
  } holds
  
  def LemmaCommutative$2(A: String, B: String, n: BigInt): Boolean = {
    require(n >= 2 && A + B == B + A)
    (A + B) + power(A, n-1) == A + (B + power(A, n-1))
  } holds
  
  def LemmaCommutative$3(A: String, B: String, n: BigInt): Boolean = {
    require(n >= 2 && A + B == B + A)
    A + (power(A, n-1) + B) == (A + power(A, n-1)) + B
  } holds
  
  def LemmaCommutative$4(A: String, B: String, n: BigInt): Boolean = {
    require(n >= 2 && A + B == B + A)
    (A + power(A, n-1)) + B == power(A, n) + B
  } holds
  
  def emptyStringCommutes(A: String): Boolean = {
    A + "" == "" + A
  } holds
  
  def LemmaRightEquality(A: String, B: String, C: String): Boolean = {
    require(B == C)
    A+B == A+C
  } holds
  
  def LemmaLeftEquality(A: String, B: String, C: String): Boolean = {
    require(A == B)
    A+C == B+C
  } holds

  /*def LemmaCommutative(A: String, B: String, n: BigInt): Boolean = {
    require(A + B == B + A && n >= 0)
    B + power(A, n) == power(A, n) + B because {
      if(n == 0) power(A, 0) == "" && emptyStringCommutes(B)
      else if(n == 1) power(A, 1) == A && B + A == A + B
      else {
        B + power(A, n)         ==| LemmaCommutative$0(A,B,n) |
        (B + A) + power(A, n-1) ==| LemmaCommutative$1(A,B,n) |
        (A + B) + power(A, n-1) ==| LemmaCommutative$2(A,B,n) |
        A + (B + power(A, n-1)) ==| LemmaCommutative(A, B, n-1) |
        A + (power(A, n-1) + B) ==| LemmaCommutative$3(A,B,n) |
        (A + power(A, n-1)) + B ==| LemmaCommutative$4(A,B,n) |
        power(A, n) + B
      } qed
    }
  } holds*/
  
  // B + nA == nA + B
  def LemmaPowerKeepsCommutativity(A: String, B: String, n: BigInt): Boolean = {
    require(A + B == B + A && n >= 0)
    (
      if(n == 0) power(A, 0) == "" && emptyStringCommutes(B)
      else if(n == 1) power(A, 1) == A && B + A == A + B
      else {
         LemmaCommutative$0(A,B,n) &&
         LemmaCommutative$1(A,B,n) &&
         LemmaCommutative$2(A,B,n) && 
         LemmaPowerKeepsCommutativity(A, B, n-1) &&
         LemmaCommutative$3(A,B,n) &&
         LemmaCommutative$4(A,B,n)
      }
    ) && B + power(A, n) == power(A, n) + B 
  } holds
  
  // n(A+B) = nA + nB
  def LemmaDblPowerKeepsCommutativity(A: String, B: String, n: BigInt): Boolean = {
    require(A + B == B + A && n >= 0)
    if(n == 0) power(A, 0) == "" && power(B, 0) == ""    && power(A + B, n) == power(A, n) + power(B, n)
    else if(n == 1) power(A, 1) == A && power(B, 1) == B && power(A + B, n) == power(A, n) + power(B, n)
    else {
      power(A + B, n) == (A + B) + power(A + B, n - 1) &&
      LemmaDblPowerKeepsCommutativity(A, B, n-1) &&
       (A + B) + power(A + B, n - 1) == (A + B) + (power(A, n-1) + power(B, n-1)) &&
       LemmaAssociativity(A, B, power(A, n-1) + power(B, n-1)) &&
       (A + B) + (power(A, n-1) + power(B, n-1)) == A + (B + (power(A, n-1) + power(B, n-1))) &&
       LemmaAssociativity(B, power(A, n-1), power(B, n-1)) &&
       A + (B + (power(A, n-1) + power(B, n-1))) == A + ((B + power(A, n-1)) + power(B, n-1)) &&
       LemmaPowerKeepsCommutativity(A, B, n - 1) &&
       //B + power(A, n-1) == power(A, n-1) + B && 
       A + ((B + power(A, n-1)) + power(B, n-1)) == A + ((power(A, n-1) + B) + power(B, n-1)) &&
       LemmaAssociativity(power(A, n-1), B, power(B, n-1)) &&
       A + ((power(A, n-1) + B) + power(B, n-1)) == A + (power(A, n-1) + (B + power(B, n-1))) &&
       LemmaAssociativity(A, power(A, n-1), (B + power(B, n-1))) &&
       A + (power(A, n-1) + (B + power(B, n-1))) == (A + power(A, n-1)) + (B + power(B, n-1)) &&
      (A + power(A, n-1)) + (B + power(B, n-1)) == power(A, n) + power(B, n)
    } &&
    power(A + B, n) == power(A, n) + power(B, n)
  } holds
  
  // A + n(B+A) == n(A+B) + A
  def LemmaPowerEquivalence(A: String, B: String, n: BigInt): Boolean = {
    require(n >= 0)
    if(n == 0)      power(B + A, n) == "" && emptyStringCommutes(A)  && A + power(B + A, n) == power(A + B, n) + A
    else if(n == 1) power(B + A, 1) == B + A && LemmaAssociativity(A, B, A) && A + power(B + A, n) == power(A + B, n) + A
    else {
      A + power(B + A, n) == A + ((B + A) + power(B + A, n - 1)) &&
      LemmaAssociativity(B, A, power(B + A, n - 1)) &&
      A + ((B + A) + power(B + A, n - 1)) == A + (B + (A + power(B + A, n - 1))) &&
      LemmaPowerEquivalence(A, B, n-1) &&
      A + (B + (A + power(B + A, n - 1))) == A + (B + (power(A + B, n - 1) + A)) &&
      LemmaAssociativity(B, power(A + B, n - 1), A) &&
      A + (B + (power(A + B, n - 1) + A)) == A + ((B + power(A + B, n - 1)) + A) &&
      LemmaPowerEquivalence(B, A, n-1) &&
      A + ((B + power(A + B, n - 1)) + A) == A + ((power(B + A, n - 1) + B) + A) &&
      LemmaAssociativity4_1_3(A, power(B + A, n - 1), B, A) &&
      A + ((power(B + A, n - 1) + B) + A) == ((A + power(B + A, n - 1)) + B) + A &&
      LemmaPowerEquivalence(A, B, n-1) &&
      ((A + power(B + A, n - 1)) + B) + A == ((power(A + B, n - 1) + A) + B) + A &&
      LemmaAssociativity(power(A + B, n - 1), A, B) &&
      ((power(A + B, n - 1) + A) + B) + A ==  (power(A + B, n - 1) + (A + B)) + A &&
      LemmaPowerRight(A + B, n) &&
      (power(A + B, n - 1) + (A + B)) + A ==  power(A + B, n) + A
    } &&
    A + power(B + A, n) == power(A + B, n) + A
  } holds
  
  def lemmaCommuteSize(A: String, B: String): Boolean = {
    (A+B).bigLength == (B+A).bigLength
  } holds
  
  def reduceForm2(A: String, B: String, C: String, D: String, E: String, s: String, r: String, t: String, m: String, k: String) = {
    require(A+(A+C+B)+B == D+(D+C+E)+E &&
      k == r + s &&
      m == s + r &&
      C == r + s + t && C == t + (s + r) &&
      D == A + k &&
      B == m + E
    )
    (A+(A+C+(m + E)))+(m + E) == (D+(D+C+E))+E &&
    LemmaAssociativity(A+(A+C+(m + E)), m, E) &&
    ((A+(A+C+(m + E)))+m) + E == (D+(D+C+E))+E &&
    LemmaRightSimplification((A+(A+C+(m + E)))+m, D+(D+C+E), E) &&
    (A+(A+C+(m + E)))+m == D+(D+C+E) &&
    (A+(A+C+(m + E)))+m == (A+k)+(A+k+C+E) &&
    LemmaAssociativity(A, A+C+(m + E), m) && LemmaAssociativity(A, k, A+k+C+E) &&
    A+((A+C+(m + E))+m) == A+(k+(A+k+C+E)) &&
    LemmaLeftSimplification(A, ((A+C+(m + E))+m), (k+(A+k+C+E))) &&
    A+C+(m+E)+m == k+(A+k+C+E) &&
    A+(r+s+t)+(m+E)+m == k+(A+k+C+E) && C == t+(s+r) &&
    A+(r+s+t)+(m+E)+m == k+(A+k+(t+(s+r))+E) && m == s+r &&
    A+(r+s+t)+((s+r)+E)+(s+r) == k+(A+k+(t+(s+r))+E) && k == r+s &&
    A+(r+s+t)+((s+r)+E)+(s+r) == (r+s)+(A+k+(t+(s+r))+E) && 
      (A+((r+s) + t)) + ((s+r)+E)+(s+r)               ==  (r+s)+(A+(r+s)+(t+(s+r))+E) &&
      LemmaAssociativity(A+((r+s) + t), (s+r)+E, s+r) &&
      (A+((r+s) + t)) + ((s+r)+E)+(s+r) == (A+((r+s) + t)) + (((s+r)+E)+(s+r)) &&
      LemmaAssociativity(A, r+s, t) &&
      LemmaLeftEquality(A+((r+s) + t), (A+(r+s))+t, ((s+r)+E)+(s+r)) &&
      (A+((r+s) + t)) + (((s+r)+E)+(s+r)) ==
      ((A+(r+s))+t)   + (((s+r)+E)+(s+r)) &&
      LemmaAssociativity(A+(r+s), t, (((s+r)+E)+(s+r))) &&
      ((A+(r+s))+t)   + (((s+r)+E)+(s+r)) ==
      (A+(r+s))+(t   + (((s+r)+E)+(s+r))) &&
                                                      LemmaAssociativity4_1_3(A, r+s, t+(s+r), E) &&
                                                        A + ((r+s) + (t+(s+r)) + E) == ((A + (r+s)) + (t+(s+r))) + E &&
                                                      ((A+(r+s))+(t+(s+r)))+E == A+(((r+s)+(t+(s+r))+E)) &&
                                                      LemmaRightEquality(r+s, A+(r+s)+(t+(s+r))+E, A+((r+s)+(t+(s+r))+E)) &&
                                                      (r+s)+(A+(r+s)+(t+(s+r))+E) == (r+s)+(A+((r+s)+(t+(s+r))+E)) &&
                                                      LemmaAssociativity(r+s, A, ((r+s)+(t+(s+r))+E)) &&
                                                      (r+s)+(A+((r+s)+(t+(s+r))+E)) == ((r+s)+A)+((r+s)+(t+(s+r))+E) &&
      (A+(r+s))+(t   + (((s+r)+E)+(s+r))) == (A+((r+s)+t))+((s+r)+E)+(s+r) &&
      (A+((r+s)+t))+((s+r)+E)+(s+r) == (r+s)+(A+(r+s)+(t+(s+r))+E) &&
      (r+s)+(A+(r+s)+(t+(s+r))+E) == ((r+s)+A)+((r+s)+(t+(s+r))+E)
      (A+(r+s))+(t   + (((s+r)+E)+(s+r))) ==  ((r+s)+A)+((r+s)+(t+(s+r))+E) &&
    lemmaCommuteSize(r+s, A) &&
    ((r+s)+A).bigLength == (A+(r+s)).bigLength &&
    LemmaLeftSizeSimplification(A + (r+s), (t + (((s+r)+E)+(s+r))), (r+s)+A, ((r+s)+(t+(s+r))+E)) &&
    A + (r+s) == (r+s) + A && t + (((s+r)+E)+(s+r)) == ((r+s)+(t+(s+r))+E) &&
    LemmaAssociativity4_1_2(t, s+r, E, s+r) &&
    t + (((s+r)+E)+(s+r)) == (t + (s+r))+(E+(s+r)) &&
    LemmaAssociativity4_1_2_2(r+s, t, s+r, E) &&
    ((r+s)+(t+(s+r))+E) == ((r+s)+t)+((s+r)+E) &&
    (t + (s+r))+(E+(s+r)) == ((r+s)+t)+((s+r)+E) &&
    lemmaCommuteSize(s+r, E) &&
    ((s+r)+E).bigLength == (E+(s+r)).bigLength &&
    LemmaRightSizeSimplification((t + (s+r)), (E+(s+r)) , ((r+s)+t), ((s+r)+E)) &&
    E + (s+r) == (s+r) + E
  } ensuring { (res: Boolean) =>
    res && A + (r+s) == (r+s) + A && E + (s+r) == (s+r) + E
  }
  
  def reduceFormCIsr(A: String, B: String, C: String, D: String, E: String, s: String, r: String, m: String, k: String) = {
    require(A+(A+C+B)+B == D+(D+C+E)+E &&
      k == r + s &&
      m == s + r &&
      C == r &&
      D == A + k &&
      B == m + E
    )
    check(
      (A+(A+C+(m + E)))+(m + E) == (D+(D+C+E))+E &&
    LemmaAssociativity(A+(A+C+(m + E)), m, E) &&
    ((A+(A+C+(m + E)))+m) + E == (D+(D+C+E))+E &&
    LemmaRightSimplification((A+(A+C+(m + E)))+m, D+(D+C+E), E) &&
    (A+(A+C+(m + E)))+m == D+(D+C+E) &&
    (A+(A+C+(m + E)))+m == (A+k)+(A+k+C+E) &&
    LemmaAssociativity(A, A+C+(m + E), m) && LemmaAssociativity(A, k, A+k+C+E) &&
    A+((A+C+(m + E))+m) == A+(k+(A+k+C+E)) &&
    LemmaLeftSimplification(A, ((A+C+(m + E))+m), (k+(A+k+C+E))) &&
    A+C+(m+E)+m == k+(A+k+C+E) &&
    A+r+(m+E)+m == k+(A+k+C+E) && C == r &&
    A+r+(m+E)+m == k+(A+k+r+E) && m == s+r &&
    A+r+((s+r)+E)+(s+r) == k+(A+k+r+E) && k == r+s &&
    A+r+((s+r)+E)+(s+r) == (r+s)+(A+k+r+E)) && 
    check(  ((A+r) + ((s+r)+E))+(s+r)               ==  (r+s)+(((A+(r+s))+r)+E)) &&
    check( LemmaAssociativity5_2_3__1_2_2(A, r, s, r, E) &&
      (A+r) + ((s+r)+E) == (A+(r+s))+(r+E) &&
      LemmaLeftEquality((A+r) + ((s+r)+E), (A+(r+s))+(r+E), s+r) &&
      (A+r) + ((s+r)+E) + (s+r) == ((A+(r+s))+(r+E)) + (s+r) &&
      LemmaAssociativity((A+(r+s)), (r+E), (s+r)) &&
      ((A+(r+s))+(r+E)) + (s+r) == (A+(r+s))+((r+E) + (s+r))) &&
                                             check( LemmaAssociativity4_1_3(A, r+s, r, E) &&
                                                A + ((r+s) + r + E) == ((A + (r+s)) + r) + E &&
                                                ((A+(r+s))+r)+E == A+(((r+s)+r+E)) &&
                                              LemmaRightEquality(r+s, A+(r+s)+r+E, A+((r+s)+r+E)) &&
                                              (r+s)+(A+(r+s)+r+E) == (r+s)+(A+((r+s)+r+E)) &&
                                              LemmaAssociativity(r+s, A, ((r+s)+r+E)) &&
                                              (r+s)+(A+((r+s)+r+E)) == ((r+s)+A)+((r+s)+r+E)) &&
      (A+(r+s))+((r+E) + (s+r)) == ((A+(r+s))+(r+E)) + (s+r) &&
      ((A+(r+s))+(r+E)) + (s+r) == (r+s)+(((A+(r+s))+r)+E) &&
      (r+s)+(((A+(r+s))+r)+E) == ((r+s)+A)+((r+s)+r+E) &&
      (A+(r+s))+((r+E) + (s+r)) ==  ((r+s)+A)+((r+s)+r+E) &&
    lemmaCommuteSize(r+s, A) &&
    ((r+s)+A).bigLength == (A+(r+s)).bigLength &&
    LemmaLeftSizeSimplification(A + (r+s), ((r+E) + (s+r)), (r+s)+A, ((r+s)+r+E)) &&
    check(A + (r+s) == (r+s) + A) &&
    ((r+E) + (s+r)) == ((r+s)+r+E) &&
    LemmaAssociativity(r, E, s+r) &&
    ((r+E) + (s+r)) == r+(E+(s+r)) &&
    LemmaAssociativity4_1_3(r, E, s, r) &&
    ((r+s)+r)+E == r+((s+r)+E) &&
    r+(E+(s+r)) == r+((s+r)+E) &&
    LemmaLeftSizeSimplification(r, E+(s+r) , r, (s+r)+E) &&
    check(E + (s+r) == (s+r) + E)
  } ensuring { (res: Boolean) =>
    res && A + (r+s) == (r+s) + A && E + (s+r) == (s+r) + E
  }

  def lemmaPropagateCommutativity(B: String, k: String, E: String): Boolean = {
    require(B == k + E && E + k == k + E)
    LemmaLeftEquality(B, k + E, k) &&
    B + k == k + E + k &&
    LemmaAssociativity(k, E, k) &&
    k + E + k == k + (E + k) &&
    LemmaRightEquality(k, E + k, k + E) &&
    k + (E + k) == k + (k + E) &&
    LemmaRightEquality(k, k + E, B) &&
    k + (k + E) == k + B &&
    B + k == k + B
  } holds
  
 def lemmaPropagateCommutativity2(A: String, k: String, D: String): Boolean = {
    require(D == A + k && A + k == k + A)
    LemmaLeftEquality(D, A + k, k) &&
    D + k == A + k + k &&
    LemmaLeftEquality(D, A + k, k + A) &&
    A + k + k == k + A + k &&
    LemmaAssociativity(k, A, k) &&
    k + A + k == k + (A + k) &&
    LemmaRightEquality(k, A + k, D) &&
    k + (A + k) == k + D &&
    D + k == k + D
  } holds
  
  def lemmaReverse(A: String, F: String, B: String, kl: String, kr: String): Boolean = {
    require(B + kr == kr + B && F + kr == kl + F && A + kl == kl + A)
    LemmaAssociativity4_2_3(A, F, B, kr) &&
    A+F+B+kr == (A+F) + (B+kr) &&
    LemmaRightEquality(A+F, B+kr, kr+B) &&
    (A+F) + (B+kr) == (A+F) + (kr+B) &&
    LemmaAssociativity4_1_2(A, F, kr, B) &&
    (A+F) + (kr+B) == A+(F + kr)+B &&
    LemmaLeftEquality(F+kr, kl+F, B) &&
    LemmaRightEquality(A, (F+kr)+B, (kl+F)+B) &&
    A+(F + kr)+B == A+(kl + F)+B &&
    LemmaAssociativity4_1_2(A, kl, F, B) &&
    A+(kl + F)+B == (A+kl) + (F+B) &&
    LemmaLeftEquality(A+kl, kl+A, F+B) &&
    (A+kl) + (F+B) == (kl+A) + (F+B) &&
    LemmaAssociativity4_1_2(kl, A, F, B) &&
    (kl+A) + (F+B) == kl+(A+F+B) &&
    (A+F+B)+kr == kl + (A+F+B)
  } holds
  
  def theoremCase1(n: Nat, A: String, B: String, C: String, D: String, E: String, F: String, r: String, s: String): Boolean = {
    require{
      val f = (n: Nat) => fc(n, A, B, C)
      val g = (n: Nat) => fc(n, D, E, F)
      C + (s+r) == (r+s) + C &&
      D == A + (r + s) &&
      B == (s + r) + E &&
      E + (s+r) == (s+r) + E &&
      A+(r+s) == (r+s) + A &&
      C == F
    }
    val f = (n: Nat) => fc(n, A, B, C)
    val g = (n: Nat) => fc(n, D, E, F)
    (
      n match {
        case Zero => f(Zero) == g(Zero) && 
          f(Zero) == C &&
          LemmaLeftEquality(f(Zero), C, s+r) &&
          f(Zero) + (s+r) == C + (s+r) &&
          C + (s+r) == (r+s) + C &&
          LemmaRightEquality(r+s, C, f(Zero)) &&
          (r+s) + C == (r+s) + f(Zero) &&
          f(Zero) + (s+r) == (r+s) + f(Zero)
        case Succ(np) => 
          theoremCase1(np, A, B, C, D, E, F, r, s) &&
          (r+s) + f(np) == f(np) + s + r &&
          f(n) == A + f(np) + B &&
            A + f(np) + B == A + f(np) + ((s + r) + E) &&
            LemmaAssociativity(A, f(np), s+r+E) &&
            A + f(np) + ((s + r) + E) == A + (f(np) + ((s + r) + E)) &&
            LemmaAssociativity(f(np), s+r, E) &&
            LemmaRightEquality(A, f(np) + ((s + r) + E), (f(np) + (s + r)) + E) &&
            A + (f(np) + ((s + r) + E)) == A + ((f(np) + (s + r)) + E) &&
            f(np) + (s+r) == (r+s) + f(np) &&
            LemmaLeftEquality(f(np) + (s+r), (r+s) + f(np), E) &&
            ((f(np) + (s + r)) + E) ==  (((r+s) + f(np)) + E) &&
            LemmaRightEquality(A, ((f(np) + (s + r)) + E), (((r+s) + f(np)) + E)) &&
            A + ((f(np) + (s + r)) + E) == A + (((r + s) + f(np)) + E) &&
            LemmaAssociativity4_1_3(A, (r+s), f(np), E) &&
            A + (((r + s) + f(np)) + E) == (A + (r+s)) + f(np) + E &&
            (A + (r+s)) + f(np) + E == D + f(np) + E &&
            D + f(np) + E == D + g(np) + E &&
            D + g(np) + E == g(n) &&
            f(n) == g(n) &&
          lemmaPropagateCommutativity(B, s+r, E) &&
          B + (s+r) == (s+r) + B &&
          lemmaPropagateCommutativity2(A, r+s, D) &&
          A + (r+s) == (r+s) + A &&
          lemmaReverse(A, f(np), B, r+s, s+r) &&
          (A + f(np) + B) + (s+r) == (r+s) + (A + f(np) + B) &&
          LemmaLeftEquality(f(n), A + f(np) + B, s+r) &&
          (A + f(np) + B) + (s+r) == f(n) + (s+r) &&
          LemmaRightEquality(r+s, (A + f(np) + B), f(n))  &&
          (r+s) + (A + f(np) + B) == (r+s) + f(n) &&
          f(n) + (s+r) == (r+s) + f(n)
      }
    ) && (f(n) == g(n) && (r+s) + f(n) == f(n) + (s + r))
  } holds
  
  def equalitySimpleC(C: String, s: String, r: String): Boolean = {
    require(C == r)
    LemmaLeftEquality(C, r, s+r) &&
    C + (s+r) == r + (s+r)&&
    LemmaAssociativity(r, s, r) &&
    r + (s+r) == (r + s)+r &&
    LemmaRightEquality(r+s, r, C) &&
    (r+s)+r == (r+s) + C
  } ensuring {
    (res: Boolean) => C + (s+r) == (r+s) + C
  }
  
  def EqualityBetweenListPrinters(n: Nat, A: String, B: String, C: String, D: String, E: String, F: String) = {
    require{
      val f = (n: Nat) => fc(n, A, B, C)
      val g = (n: Nat) => fc(n, D, E, F)
      f(Zero) == g(Zero) &&
      f(Succ(Zero)) == g(Succ(Zero))  &&
      f(Succ(Succ(Zero))) == g(Succ(Succ(Zero)))}
    val f = (n: Nat) => fc(n, A, B, C)
    val g = (n: Nat) => fc(n, D, E, F)
    if(
      (if( f(Zero) == C &&
        g(Zero) == F &&
        C == F &&
        f(Succ(Zero)) == A+C+B &&
        g(Succ(Zero)) == D+F+E &&
        A+C+B == D+C+E &&
        f(Succ(Succ(Zero))) == A+(A+C+B)+B &&
        g(Succ(Succ(Zero))) == D+(D+F+E)+E &&
        A+(A+C+B)+B == D+(D+C+E)+E) {
      if(E.bigLength == B.bigLength) {
        check(
                                                 (A+C)+B == (D+C)+E &&
          LemmaRightSizeSimplification(A+C,B,D+C,E)  &&     B == E &&
          LemmaRightSimplification(A+C,D+C,B) &&          A+C == D+C  &&
          LemmaRightSimplification(A,D,C) &&                A == D) &&
        check(f(n) == g(n))
      } else {
      n match {
      case Zero => 
        check(f(n) == g(n))
      case Succ(Zero) =>
        check(f(n) == g(n))
      case Succ(np) => 
        if(E.bigLength < B.bigLength) {
          val m = Lemma006SuffixIntroduce(D+C, E, A+C, B)
          check(B == m + E && D+C == (A+C) + m &&    // ACB = DCE <=> ACm = DC
          LemmaRightGreaterSmaller(D+C, E, A+C, B) &&
          (D+C).bigLength > (A+C).bigLength &&
          LemmaLength(D, C) && LemmaLength(A, C) &&
          D.bigLength + C.bigLength > A.bigLength + C.bigLength &&
          D.bigLength > A.bigLength &&
          LemmaAssociativity(A, C, m) &&
          D+C == A+(C+m)) && {
            val k = Lemma005PrefixIntroduce(A, C+m, D, C)
            check(D == A+k &&                    // ACm = DC <=> Cm = kC
            (A+k)+C == (A+C)+m &&
            LemmaAssociativity(A, k, C) && LemmaAssociativity(A, C, m) &&
            A+(k+C) == A+(C+m) &&
            LemmaLeftSimplification(A, k+C, C+m) &&
            C+m == k+C) && {
              if(C.bigLength > k.bigLength) {
                val (r, s, t) = LemmaCommutation3(C, m, k)
                check(k == r + s &&
                    m == s + r &&
                    C == r + s + t && C == t + (s + r) &&
                    D == A + k &&
                    LemmaRightEquality(A, k, r+s) &&
                    A + k == A + (r+s) &&
                    D == A + (r+s) &&
                    B == m + E &&
                    LemmaLeftEquality(m, s+r, E) &&
                    m + E == (s+r) + E &&
                    B == (s+r) + E) &&
                check (reduceForm2(A, B, C, D, E, s, r, t, m, k)) &&
                check (theoremCase1(n, A, B, C, D, E, F, r, s)) &&
                check (f(n) == g(n))
              } else {
                val (r, s) = LemmaCommutation1(C, m, k)
                check(
                  k == r + s &&
                  m == s + r &&
                  C == r) &&
                check(C == r) && 
                check(C == r) &&
                check(equalitySimpleC(C, s, r)) &&
                check(LemmaRightEquality(r+s, r, C) &&
                  (r+s)+r == (r+s) + C) &&
                check(LemmaRightEquality(A, k, r+s) &&
                  A + k == A + (r + s)) &&
                check(reduceFormCIsr(A, B, C, D, E, s, r, m, k)) &&
                check(theoremCase1(n, A, B, C, D, E, F, r, s)) &&
                check(f(n) == g(n))
              }
            }
          }
        } else {
          val m = Lemma006SuffixIntroduce(A+C, B, D+C, E)
          check(E == m + B && A+C == (D+C) + m &&    // ACB = DCE <=> ACm = DC
          LemmaRightGreaterSmaller(A+C, B, D+C, E) &&
          (A+C).bigLength > (D+C).bigLength &&
          LemmaLength(A, C) && LemmaLength(D, C) &&
          A.bigLength + C.bigLength > D.bigLength + C.bigLength &&
          A.bigLength > D.bigLength &&
          LemmaAssociativity(D, C, m) &&
          A+C == D+(C+m)) && {
            val k = Lemma005PrefixIntroduce(D, C+m, A, C)
            check(A == D+k &&                    // ACm = DC <=> Cm = kC
            (D+k)+C == (D+C)+m &&
            LemmaAssociativity(D, k, C) && LemmaAssociativity(D, C, m) &&
            D+(k+C) == D+(C+m) &&
            LemmaLeftSimplification(D, k+C, C+m) &&
            C+m == k+C)  && {
              if(C.bigLength > k.bigLength) {
                val (r, s, t) = LemmaCommutation3(C, m, k)
                check(k == r + s &&
                m == s + r &&
                C == r + s + t && C == t + (s + r) &&
                A == D + k &&
                LemmaRightEquality(D, k, r+s) &&
                D + k == D + (r+s) &&
                A == D + (r+s) &&
                E == m + B &&
                LemmaLeftEquality(m, s+r, B) &&
                m + B == (s+r) + B &&
                E == (s+r) + B) &&
                check(reduceForm2(D, E, C, A, B, s, r, t, m, k)) &&
                check(theoremCase1(n, D, E, C, A, B, F, r, s)) &&
                check(f(n) == g(n))
              } else {
                val (r, s) = LemmaCommutation1(C, m, k)
                check(
                  k == r + s &&
                  m == s + r &&
                  C == r) &&
                check(C == r) &&
                check(
                  equalitySimpleC(C, s, r)) &&
                check(LemmaRightEquality(r+s, r, C) &&
                  (r+s)+r == (r+s) + C) &&
                check(LemmaRightEquality(D, k, r+s) &&
                  D + k == D + (r + s)) &&
                check(reduceFormCIsr(D, E, C, A, B, s, r, m, k)) &&
                check(theoremCase1(n, D, E, F, A, B, C, r, s)) &&
                check(f(n) == g(n))
              }
            }
          }
        }
      }
      }
    } else error[Boolean]("this should not happen"))
      && f(n) == g(n))
      true
    else  error[Boolean]("this should not happen")
    
  } ensuring { (res: Boolean) =>
    val f = (n: Nat) => fc(n, A, B, C)
    val g = (n: Nat) => fc(n, D, E, F)
    res && f(n) == g(n)
  }
}