import leon.lang._
import leon.annotation._
import leon.collection._

object CalcDiff {

    /** This is the main property of be proven. */
    def algorithmCheck(ls: List[BigInt]): Boolean = ({
        ls == rebuildList(differences(ls))
    }) holds

    /** Function used to build the difference List
      * for a given List.
      */
    def differences(ls: List[BigInt]): List[BigInt] = ({
        subDifferences(ls, 0)
    }) ensuring (res => res.size == ls.size && headEquality(res, ls) && diffProperty(res, ls, 0) && rebuildList(res) == ls)

    private def subDifferences(subLs: List[BigInt], prev: BigInt): List[BigInt] = (subLs match {
        case Nil() => Nil[BigInt]()
        case head :: tail => (head - prev) :: subDifferences(tail, head)
    }) ensuring(res => res.size == subLs.size && diffProperty(res, subLs, prev) && subRebuildList(res, prev) == subLs)

    /** Function used to rebuild the original List
      * from its difference List.
      */
    def rebuildList(ls: List[BigInt]): List[BigInt] = ({
        subRebuildList(ls, 0)
    }) ensuring (res => res.size == ls.size && headEquality(res, ls) && rebProperty(res, ls, 0))
    
    private def subRebuildList(subLs: List[BigInt], prev: BigInt): List[BigInt] = (subLs match {
        case Nil() => Nil[BigInt]()
        case head::tail => (head + prev) :: subRebuildList(tail, head + prev)
    }) ensuring (res => res.size == subLs.size && rebProperty(res, subLs, prev))

    /** ---------------------------------------------------
      * All the functions below were created to exclusively
      * help Leon's verification system. 
      * 
      * All of them aim to prove a certain property
      * about the code above.
      * ---------------------------------------------------
      */

    /** Returns true if the 'head' element has the
      * same value in both Lists.
      */
    private def headEquality(lsA: List[BigInt], lsB: List[BigInt]): Boolean = lsA.headOption == lsB.headOption

    /** This function attempts to check the condition
      * res(i) == ls(i) - ls(i-1), for every 0 < i < length(res).
      */
    private def diffProperty(res: List[BigInt], ls: List[BigInt], prev: BigInt): Boolean = (res, ls) match {
        case (Nil(), Nil()) => true
        case (rHead::rTail, lHead::lTail) => (rHead == lHead-prev) && diffProperty(rTail, lTail, lHead)
        case default => false
    }

    /** This function attempts to check the condition
      * res(i) == ls(i) + ls(i-1), for every 0 < i < length(res).
      */
    private def rebProperty(res: List[BigInt], ls: List[BigInt], prev: BigInt): Boolean = (res, ls) match {
        case (Nil(), Nil()) => true
        case (rHead::rTail, lHead::lTail) => (rHead == lHead+prev) && rebProperty(rTail, lTail, lHead+prev)
        case default => false
    }
}
