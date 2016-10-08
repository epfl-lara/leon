package slib

import leon._
import lang._
import annotation._
import instrumentation._
import mem._
import higherorder._
import collection._
import invariant._

/**
 * This program should be analyzed together with StreamClient.
 * This is a collection of methods translated to Scala from the haskell stream library.
 * To prove a running time bound, we impose a precondition that the input stream is an infinite
 * stream of natural numbers, and the higher-order function parameters are known constant time functions.
 * We ignored methods that are not guaranteed to terminate on all streams e.g. `filter`, `dropWhile` etc.
 */
object StreamLibrary {    
  sealed abstract class LList {
    lazy val tail = {
      require(this != SNil())
      this match {
        case SCons(_, tailFun) => tailFun()        
      }
    }
    def tailOrNil = {
      this match {
        case SNil() => this
        case _ => tail
      }         
    }   
  }
  case class SCons(x: BigInt, tailFun: () => LList) extends LList
  case class SNil() extends LList  
  
  /**
   * Stream for all natural numbers starting from n
   */
  def natsFromn(n: BigInt): LList = {
    SCons(n, () => genNextNatFrom(n))
  } ensuring(res => validNatStream(res) && steps <= ?)
  
  def genNextNatFrom(n: BigInt): LList = {
    val nn = n + 1
    SCons(nn, () => genNextNatFrom(nn))
  } ensuring(_ => steps <= ?) 

  /**
   * A property that asserts that the a stream is a `natstream`
   */
  def validNatStream(s: LList): Boolean = {
    s match {
      case SCons(_, tailFun) =>
        tailFun fmatch[BigInt, Boolean] {
          case n if tailFun.is(() => genNextNatFrom(n)) => true
          case _ => false
        }      
      case _ => true
    }
  }    
  
  @ignore
  var array = Array[BigInt]()
  @extern
  def constFun1(n: BigInt): BigInt = {
    array(0)
  } ensuring (_ => steps <= 1)

  /**
   * Apply a function over all elements of a sequence.
   * Requires that the input is a `nat` stream, and `f` is
   * constFun1 which is a constant time function.
   */  
  def map(f: BigInt => BigInt, s: LList): LList = {
    require(validNatStream(s) && f.is(constFun1 _))
    s match {
      case SNil()          => SNil()
      case l @ SCons(x, _) => SCons(f(x), () => mapSusp(f, s))
    }
  } ensuring{_ => steps <= ?}

  def mapSusp(f: BigInt => BigInt, s: LList) = {
    require(validNatStream(s) && f.is(constFun1 _))
    map(f, s.tailOrNil)
  } ensuring(_ => steps <= ?)

  /**
   * The function `appendList` appends a stream to a list,
   * returning a stream of all the list elements
   * followed by all the original stream elements.
   */
  def appendList(l: List[BigInt], s: LList): LList = {
    l match {
      case Nil()         => s
      case Cons(x, tail) => SCons(x, () => appendList(tail, s))
    }
  } ensuring (_ => steps <= ?) 

  /**
   * The function repeat expects an integer and returns a
   * stream that represents infinite appends of the
   * integer to itself.
   */
  def repeat(n: BigInt): LList = {
    SCons(n, () => repeat(n))
  } ensuring (_ => steps <= ?) 

  /**
   * The function cycle expects a list and returns a
   * stream that represents infinite appends of the
   * list to itself.
   */
  def cycle(l: List[BigInt]): LList = {
    l match {
      case Nil() => SNil()
      case Cons(x, t) =>
        SCons(x, () => appendList(t, cycle(l)))
    }
  } ensuring (_ => steps <= ?)

  @extern
  def constFun2(n: BigInt): Boolean = {
    array(0) == 0
  } ensuring (_ => steps <= 1)
  
  /**
   * 'takeWhile' returns the longest prefix of the stream for which the
   * predicate p holds.
   */
  def takeWhile(p: BigInt => Boolean, s: LList): LList = {
    require(validNatStream(s) && p.is(constFun2 _))
    s match {
      case SNil()          => SNil()
      case l @ SCons(x, _) => 
        if(p(x)) 
          SCons(x, () => takeWhileSusp(p, s))
        else 
          SNil()      
    }
  } ensuring (_ => steps <= ?)

   def takeWhileSusp(p: BigInt => Boolean, s: LList): LList = {
     require(validNatStream(s) && p.is(constFun2 _))
     takeWhile(p, s.tailOrNil)
   } ensuring(_ => steps <= ?)

   @extern
  def constFun3(n: BigInt, m: BigInt): BigInt = {
    array(0)
  } ensuring (_ => steps <= 1)
  
  /**
   * 'scan' yields a stream of successive reduced values from:
   *  scan f z [x1, x2, ...] == [z, z `f` x1, (z `f` x1) `f` x2, ...]
   */
  def scan(f: (BigInt, BigInt) => BigInt, z: BigInt, s: LList): LList = {
    require(validNatStream(s) && f.is(constFun3 _))
    s match {
      case SNil()          => SNil()
      case l @ SCons(x, _) =>
        val r = f(z, x)
        SCons(z, () => scanSusp(f, r, s))
    }
  } ensuring (_ => steps <= ?)

  def scanSusp(f: (BigInt, BigInt) => BigInt, z: BigInt, s: LList) = {
    require(validNatStream(s) && f.is(constFun3 _))
    scan(f, z, s.tailOrNil)
  } ensuring(_ => steps <= ?)

  @extern
  def constFun4(n: BigInt): (BigInt, BigInt) = {
    (array(0), array(0))
  } ensuring (_ => steps <= 1)
  
  /**
   * The unfold function is similar to the unfold for lists. Note
   * there is no base case: all streams must be infinite.
   */
  def unfold(f: BigInt => (BigInt, BigInt), c: BigInt): LList = {
    require(f.is(constFun4 _))
    val (x, d) = f(c)
    SCons(x, () => unfold(f, d))
  } ensuring(_ => steps <= ?)
  
  /**
   * The 'isPrefixOf' function returns True if the first argument is
   * a prefix of the second.
   */
  def isPrefixOf(l: List[BigInt], s: LList): Boolean = {
    require(validNatStream(s))
    s match {
      case SNil()          =>
        l match {
          case Nil() => true
          case _ => false
        }
      case ss @ SCons(x, _) =>
        l match {
          case Nil() => true
          case ll @ Cons(y, tail) =>
            if(x == y) isPrefixOf(tail, s.tailOrNil)
            else false
        }
    }
  } ensuring(_ => steps <= ? * l.size + ?)

  /**
   * The elements of two tuples are combined using the function
   * passed as the first argument to 'zipWith'.
   */
  def zipWith(f: (BigInt, BigInt) => BigInt, a: LList, b: LList): LList = {
    require(validNatStream(a) && validNatStream(b) && f.is(constFun3 _))
    a match {
      case SNil()          => SNil()
      case al @ SCons(x, _) =>
        b match {
          case SNil() => SNil()
          case bl @ SCons(y, _) =>
            SCons(f(x, y), () => zipWithSusp(f, al, bl))
        }
    }
   } ensuring(_ => steps <= ?)

  def zipWithSusp(f: (BigInt, BigInt) => BigInt, a: LList, b: LList) = {
    require(validNatStream(a) && validNatStream(b) && f.is(constFun3 _))
    zipWith(f, a.tailOrNil, b.tailOrNil)
  } ensuring(_ => steps <= ?)  
}
