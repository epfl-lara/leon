package haskell

import leon._
import lang._
import annotation._
import instrumentation._
import mem._
import higherorder._
import collection._
import invariant._

/**
 * This is a collection of methods of the hashkell stream library.
 * To prove a running time bound, we fix the input stream as an infinite
 * stream of natural numbers.
 * We ignored methods that may be possibly non-terminating.
 */
object HaskellStreamLibrary {    

  /**
   *  An infinite integer stream.
   *  Technically, the data structure is *not* infinite but the tail has a higher-order function.
   */
  sealed abstract class LList {
    lazy val tail = {
      require(this != SNil())
      this match {
        case SCons(_, tailFun) => tailFun()        
      }
    }
    
    // this will not modify state
    def tailVal = {
      require(this != SNil())      
      tail*
    }

    //@inline
    def tailCached = {    
      this match {
        case SNil() => true
        case _ => tail.cached         
      }
    }

    def tailOrNil = {
      this match {
        case SNil() => this
        case _ => tail
      }         
    }   
  }
  private case class SCons(x: BigInt, tailFun: () => LList) extends LList
  private case class SNil() extends LList
  
  /*sealed abstract class ValOrSusp {
    // ideally, fval should not be called on `Val` as it would unnecessarily cache it.
    lazy val fval = {
      this match {
        case Susp(f) => f()
        case Val(x)  => x
      }
    }
  }
  case class Val(x: LList) extends ValOrSusp
  case class Susp(fun: () => LList) extends ValOrSusp*/
  
  /**
   * Stream for all natural numbers starting from n
   */
  def natsFromn(n: BigInt): LList = {
    SCons(n, () => genNextNatFrom(n))
  }
  
  @invisibleBody
  def genNextNatFrom(n: BigInt): LList = {
    val nn = n + 1
    SCons(nn, () => genNextNatFrom(nn))
  } ensuring(_ => time <= ?) // Orb result: ??

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

  /**
   * Apply a function over all elements of a sequence.
   * Requires that the inpu is a `nat` stream.
   */
  def map(f: BigInt => BigInt, s: LList): LList = {
    require(validNatStream(s))
    s match {
      case SNil()          => SNil()
      case l @ SCons(x, _) => SCons(f(x), () => mapSusp(f, s))
    }
  } ensuring{_ => 
    s match {
      case SCons(x, _) => time <= time(f(x) withState inState[BigInt]) + ?
      case _         => time <= ?       
    }
  }

  //@invisibleBody
  def mapSusp(f: BigInt => BigInt, s: LList) = {
    require(validNatStream(s))
    map(f, s.tailOrNil)
  } //ensuring(_ => time <= ?)

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
  } ensuring (_ => time <= ?) // Orb result: ??

  /**
   * The function repeat expects an integer and returns a
   * stream that represents infinite appends of the
   * integer to itself.
   */
  def repeat(n: BigInt): LList = {
    SCons(n, () => repeat(n))
  } ensuring (_ => time <= ?) // Orb result: ??

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
  } ensuring (_ => time <= ?) // Orb result: ??

  /**
   * 'takeWhile' returns the longest prefix of the stream for which the
   * predicate p holds.
   */
  private def takeWhile(p: BigInt => Boolean, s: LList): LList = {
    require(validNatStream(s))
    s match {
      case SNil()          => SNil()
      case l @ SCons(x, _) => 
        if(p(x)) 
          SCons(x, () => takeWhileSusp(p, s))
        else 
          SNil()      
    }
  } //ensuring (_ => time <= ?)

   @invisibleBody
   private def takeWhileSusp(p: BigInt => Boolean, s: LList): LList = {
     require(validNatStream(s))
     takeWhile(p, s.tailOrNil)
   } //ensuring(_ => time <= ?)

  /**
   * 'scan' yields a stream of successive reduced values from:
   *  scan f z [x1, x2, ...] == [z, z `f` x1, (z `f` x1) `f` x2, ...]
   */
  private def scan(f: (BigInt, BigInt) => BigInt, z: BigInt, s: LList): LList = {
    require(validNatStream(s))
    s match {
      case SNil()          => SNil()
      case l @ SCons(x, _) =>
        val r = f(z, x)
        SCons(z, () => scanSusp(f, r, s))
    }
  } //ensuring (_ => time <= ?)

  @invisibleBody
  private def scanSusp(f: (BigInt, BigInt) => BigInt, z: BigInt, s: LList) = {
    require(validNatStream(s))
    scan(f, z, s.tailOrNil)
  } //ensuring(_ => time <= ?)

  /**
   * The unfold function is similar to the unfold for lists. Note
   * there is no base case: all streams must be infinite.
   */
  private def unfold(f: BigInt => (BigInt, BigInt), c: BigInt): LList = {
    val (x, d) = f(c)
    SCons(x, () => unfold(f, d))
  }// ensuring(_ => time <= ?)
  
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
  } //ensuring(_ => time <= ? * l.size + ?)

  /**
   * The elements of two tuples are combined using the function
   * passed as the first argument to 'zipWith'.
   */
  private def zipWith(f: (BigInt, BigInt) => BigInt, a: LList, b: LList): LList = {
    require(validNatStream(a) && validNatStream(b))
    a match {
      case SNil()          => SNil()
      case al @ SCons(x, _) =>
        b match {
          case SNil() => SNil()
          case bl @ SCons(y, _) =>
            SCons(f(x, y), () => zipWithSusp(f, al, bl))
        }
    }
   } //ensuring(_ => time <= ?)

  @invisibleBody
  private def zipWithSusp(f: (BigInt, BigInt) => BigInt, a: LList, b: LList) = {
    require(validNatStream(a) && validNatStream(b))
    zipWith(f, a.tailOrNil, b.tailOrNil)
  } //ensuring(_ => time <= ?)

  /**
   * Client methods: to be moved to a different file.
   */  
  def isRepeatStream(s: LList): Boolean = {
    s match {
      case SCons(_, tailFun) =>
        tailFun fmatch[BigInt, Boolean] {
          case n if tailFun.is(() => repeat(n)) => true
          case _ => false
        }      
      case _ => true
    }
  }
  
  /**
   * note cycle stream calls `appendList`
   */
  def isCycleStream(ins: LList): Boolean = {
    ins match {
      case SCons(_, tailFun) =>
        tailFun fmatch[List[BigInt], LList, Boolean] {
          case (l, s)  if tailFun.is(() => appendList(l, s)) => true
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
  } ensuring (_ => time <= 1)
  
  /**
   * A property that is true if `ins` is a stream composed of map 
   * and the function applied over a map is a constant time function 
   */
  def isMapStream(ins: LList): Boolean = {
    ins match {
      case SCons(_, tailFun) =>
        tailFun fmatch[BigInt => BigInt, LList, Boolean] {
          case (f, s)  if tailFun.is(() => mapSusp(f, s)) => 
            f.is(constFun1 _) //&& isMapStream(ins.tailVal)
          case _ => false
        }      
      case _ => true
    }
  }
  
  def mapClient(n: BigInt) = {
    require(n >= 0)
    nthElemAfterMap(n, map(constFun1, natsFromn(0)))
  }

  def nthElemAfterMap(n: BigInt, s: LList): BigInt = {
    require(n >= 0 && isMapStream(s))
    s match {
      case SNil() => BigInt(0)
      case s @ SCons(x, _) =>
        if (n == 0) x
        else nthElemAfterMap(n - 1, s.tailOrNil)
    }
  } ensuring (_ => time <= ? * n + ?) // Orb result: ??
  
  @invisibleBody  
  def getnthElem(n: BigInt, s: LList): BigInt = {
    require(n >= 0) // && isMapStream(s))
    s match {
      case SNil() => BigInt(0)
      case s @ SCons(x, _) =>
        if (n == 0) x
        else getnthElem(n - 1, s.tailOrNil)
    }
  } /*ensuring (_ => 
    //time <= ? * n + ?
    if(isRepeatStream(s)) time <= ? * n + ? 
    else if(isMapStream(s)) time <= ? * n + ? 
    else if(isAppendStream(s)) time <= ? * n + ?       
    else true  
    ) */// Orb result: time <=  27 * n + 4
  

  /*def nthElemInNatsFromM(n: BigInt, M: BigInt) = {
    require(n >= 0)
    getnthElem(n, natsFromn(M))
  }*/ //ensuring(_ => time <= ? * n + ?) // Orb result: ??
  
  def nthElemInRepeat(n: BigInt, s: LList): BigInt = {
    require(n >= 0 && isRepeatStream(s))
    s match {
      case SNil() => BigInt(0)
      case s @ SCons(x, _) =>
        if (n == 0) x
        else nthElemInRepeat(n - 1, s.tailOrNil)
    }
  } ensuring (_ => time <= ? * n + ?) // Orb result: ??

  /*def nthElemInCycle(n: BigInt, l: List[BigInt]) = {
    require(n >= 0 && isRepeatStream(s))
    getnthElem(n, cycle(l))
  }*/ //ensuring (_ => time <= ? * n + ?) // Orb result: ??  
 

  @extern
  def p(n: BigInt): Boolean = {
    array(0) == 0
  } ensuring (_ => time <= 1)

  def nthElemAfterTakeWhile(n: BigInt) = {
    require(n >= 0)
    getnthElem(n, takeWhile(p, natsFromn(0)))
  } //ensuring (_ => time <= ? * n + ?) // Orb result: ??

  @extern
  def acc(n: BigInt, m: BigInt): BigInt = {
    array(0)
  } ensuring (_ => time <= 1)

  def nthElemAfterScan(n: BigInt, z: BigInt) = {
    require(n >= 0)
    getnthElem(n, scan(acc, z, natsFromn(0)))
  } //ensuring (_ => time <= ? * n + ?) // Orb result: ??

  @extern
  def tupFunc(n: BigInt): (BigInt, BigInt) = {
    (array(0), array(0))
  } ensuring (_ => time <= 1)

  def nthElemAfterUnfold(n: BigInt, c: BigInt) = {
    require(n >= 0)
    getnthElem(n, unfold(tupFunc, c))
  } //ensuring (_ => time <= ? * n + ?) // Orb result: ??

  def nthElemAfterZipWith(n: BigInt) = {
    require(n >= 0)
    getnthElem(n, zipWith(acc, natsFromn(0), natsFromn(0)))
  } //ensuring (_ => time <= ? * n + ?) // Orb result: ??

}
