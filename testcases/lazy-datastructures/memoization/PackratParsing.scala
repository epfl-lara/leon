import leon.lazyeval._
import leon.lazyeval.Mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
//import leon.invariant._

object PackratParsing {

  // same grammar used by Bran Ford ICFP'02 paper.
  // The code is as unoptimized as it was presented in the paper to mimic a auto-genrated code

  sealed abstract class Terminal
  case class Open() extends Terminal
  case class Close() extends Terminal
  case class Plus() extends Terminal
  case class Times() extends Terminal
  case class Digit() extends Terminal

  /*sealed abstract class List {
    def size: BigInt = {
      this match {
        case Cons(_, tail) => 1 + tail.size
        case Nil() => BigInt(0)
      }
    } ensuring(_ >= 0)
  }
  case class Cons(x: Terminal, tail: List) extends List // list of terminals
  case class Nil() extends List*/

  sealed abstract class Result
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

  @invstate
  @memoize
  def pAdd(i: BigInt): Result = {
    require((i == 0 || (i > 0 && depsEval(i-1))) &&
        pMul(i).isCached && pPrim(i).isCached &&
      // lemma inst
      (pMul(i) match {
        case Parsed(j) =>
         if(j >= 0) depsLem(j, i - 1)
          else true
        case _ => true
      }))
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
  } ensuring (res => (res match {
    case Parsed(rem) => rem < i
    case _           => true
  }))

  @invstate
  @memoize
  def pMul(i: BigInt): Result = {
    require((i == 0 || (i > 0 && depsEval(i - 1))) && pPrim(i).isCached &&
      // lemma inst
      (pPrim(i) match {
        case Parsed(j) =>
          if(j>=0) depsLem(j, i - 1)
          else true
        case _ => true
      }))
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
  } ensuring (res => (res match {
    case Parsed(rem) => rem < i
    case _           => true
  }))

  @invstate
  @memoize
  def pPrim(i: BigInt): Result = {
    require(i == 0 || (i > 0 && depsEval(i-1)))
    val char = lookup(i)
    if (char == Digit()) {
      if (i > 0)
        Parsed(i - 1) // Rule1: Prim <- Digit
      else
        Parsed(-1)  // here, we can use bot to convery that the suffix is empty
    } else if (char == Open() && i > 0) {
      pAdd(i - 1) match { // Rule 2: pPrim <- ( Add )
        case Parsed(rem) =>
          Parsed(rem)
        case _ =>
          NoParse()
      }
    } else NoParse()
  } ensuring (res => res match {
    case Parsed(rem) => rem < i
    case _           => true
  })

  def depsEval(i: BigInt): Boolean = {
    require(i >= 0)
    (pPrim(i).isCached && pMul(i).isCached && pAdd(i).isCached) &&
      (if (i == 0) true
      else depsEval(i - 1))
  }

  @traceInduct
  def evalMono(i: BigInt, st1: Set[Mem[Result]], st2: Set[Mem[Result]]) = {
    require(i >= 0)
    (st1.subsetOf(st2) && (depsEval(i) withState st1)) ==> (depsEval(i) withState st2)
  } holds

  @traceInduct
  def depsLem(x: BigInt, y: BigInt) = {
    require(x >= 0 && y >= 0)
    (x <= y && depsEval(y)) ==> depsEval(x)
  } holds

  def invokeTest(i: BigInt): Result = {
    require(i == 0 || (i > 0 && depsEval(i-1)))
    pPrim(i) match {
      case _ => pMul(i)
    }
  }


  def invoke(i: BigInt): (Result, Result, Result) = {
    require(i == 0 || (i > 0 && depsEval(i-1)))
    (pPrim(i), pMul(i), pAdd(i))
  } ensuring (res => {
    val in = Mem.inState[Result]
    val out = Mem.outState[Result]
    (if(i >0) evalMono(i-1, in, out) else true) &&
    depsEval(i) //&&
      //time <= 40*items.size + 40
  })

  def bottomup(i: BigInt): Result = {
    require(i >= 0)
    if(i == 0) invoke(i)._3
    else {
      val tailres = bottomup(i-1)
      invoke(i)._3
    }
  } ensuring(_ => depsEval(i))

}
