import leon.lazyeval._
import leon.lazyeval.Mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
//import leon.invariant._

/**
 * The packrat parser that uses the Expressions grammar presented in Bran Ford ICFP'02 paper.
 * The implementation is almost exactly as it was presented in the paper, but
 * here indices are passed around between parse functions, instead of strings.
 */
object PackratParsing {

  sealed abstract class Terminal
  case class Open() extends Terminal
  case class Close() extends Terminal
  case class Plus() extends Terminal
  case class Times() extends Terminal
  case class Digit() extends Terminal

  sealed abstract class Result {
    /**
     * Checks if the index in the result (if any) is
     * smaller than `i`
     */
    @inline
    def smallerIndex(i: BigInt) = this match {
      case Parsed(m) => m < i
      case _ => true
    }
  }
  case class Parsed(rest: BigInt) extends Result
  case class NoParse() extends Result

  /**
   * A placeholder function for now.
   */
  def lookup(i: BigInt): Terminal = {
    if(i <= -100) Open()
    else if(i <= 0) Close()
    else if(i <= 100) Plus()
    else if(i <= 200) Times()
    else Digit()
  }

  @memoize
  @invstate
  def pAdd(i: BigInt): Result = {
    require(depsEval(i) &&
      pMul(i).isCached && pPrim(i).isCached &&
      resEval(i, pMul(i))) // lemma inst

    // Rule 1: Add <- Mul + Add
    pMul(i) match {
      case Parsed(j) =>
        if (j > 0 && lookup(j) == Plus()) {
          pAdd(j - 1) match {
            case Parsed(rem) =>
              Parsed(rem)
            case _ =>
              pMul(i) // Rule2: Add <- Mul
          }
        } else pMul(i)
      case _ =>
        pMul(i)
    }
  } ensuring (res => res.smallerIndex(i) && time <= 40)

  @memoize
  @invstate
  def pMul(i: BigInt): Result = {
    require(depsEval(i) && pPrim(i).isCached &&
      resEval(i, pPrim(i)) // lemma inst
      )
    // Rule 1: Mul <- Prim *  Mul
    pPrim(i) match {
      case Parsed(j) =>
        if (j > 0 && lookup(j) == Plus()) {
          pMul(j - 1) match {
            case Parsed(rem) =>
              Parsed(rem)
            case _ =>
              pPrim(i) // Rule2: Mul <- Prim
          }
        } else pPrim(i)
      case _ =>
        pPrim(i)
    }
  } ensuring (res => res.smallerIndex(i) && time <= 40)

  @memoize
  @invstate
  def pPrim(i: BigInt): Result = {
    require(depsEval(i))
    val char = lookup(i)
    if (char == Digit()) {
      if (i > 0)
        Parsed(i - 1) // Rule1: Prim <- Digit
      else
        Parsed(-1)  // here, we can use -1 to convery that the suffix is empty
    } else if (char == Open() && i > 0) {
      pAdd(i - 1) match { // Rule 2: pPrim <- ( Add )
        case Parsed(rem) =>
          Parsed(rem)
        case _ =>
          NoParse()
      }
    } else NoParse()
  } ensuring (res => res.smallerIndex(i) && time <= 30)

  @inline
  def depsEval(i: BigInt) = i == 0 || (i > 0 && allEval(i-1))

  def allEval(i: BigInt): Boolean = {
    require(i >= 0)
    (pPrim(i).isCached && pMul(i).isCached && pAdd(i).isCached) &&(
      if (i == 0) true
      else allEval(i - 1))
  }

  @traceInduct
  def evalMono(i: BigInt, st1: Set[Mem[Result]], st2: Set[Mem[Result]]) = {
    require(i >= 0)
    (st1.subsetOf(st2) && (allEval(i) withState st1)) ==> (allEval(i) withState st2)
  } holds

  @traceInduct
  def depsLem(x: BigInt, y: BigInt) = {
    require(x >= 0 && y >= 0)
    (x <= y && allEval(y)) ==> allEval(x)
  } holds

  /**
   * Instantiates the lemma `depsLem` on the result index (if any)
   */
  @inline
  def resEval(i: BigInt, res: Result) = {
    (res match {
      case Parsed(j) =>
        if (j >= 0 && i > 1) depsLem(j, i - 1)
        else true
      case _ => true
    })
  }

  def invoke(i: BigInt): (Result, Result, Result) = {
    require(i == 0 || (i > 0 && allEval(i-1)))
    (pPrim(i), pMul(i), pAdd(i))
  } ensuring (res => {
    val in = Mem.inState[Result]
    val out = Mem.outState[Result]
    (if(i >0) evalMono(i-1, in, out) else true) &&
    allEval(i) &&
    time <= 200
  })

  /**
   * Parsing a string of length 'n+1'.
   * Word is represented as an array indexed by 'n'. We only pass around the index.
   * The 'lookup' function will return a character of the array.
   */
  def parse(n: BigInt): Result = {
    require(n >= 0)
    if(n == 0) invoke(n)._3
    else {
      val tailres = parse(n-1) // we parse the prefixes ending at 0, 1, 2, 3, ..., n
      invoke(n)._3
    }
  } ensuring(_ => allEval(n) &&
      time <= 250*n + 250)

}
