package slib

import leon._
import lang._
import annotation._
import instrumentation._
import mem._
import higherorder._
import collection._
import invariant._
import StreamLibrary._

object StreamClient {
  def mapClient(n: BigInt) = {
    require(n >= 0)
    nthElemAfterMap(n, map(constFun1, natsFromn(0)))
  }

  @inline
  def mapStream(s: LList) = {
    s match {
      case SCons(_, tfun) => tfun fmatch[BigInt => BigInt, LList, Boolean] {
          case (f, n) if tfun.is(() => mapSusp(f, n)) => true
          case _ => false
        }  
      case _              => true
    }
  }
  
  def nthElemAfterMap(n: BigInt, s: LList): BigInt = {
    require(n >= 0 && mapStream(s))
    s match {
      case SNil() => BigInt(0)
      case s @ SCons(x, _) =>
        if (n == 0) x
        else nthElemAfterMap(n - 1, s.tailOrNil)
    }
  } ensuring (_ => alloc <= ? * n + ?) 
    
  @inline
  def repeatStream(s: LList) = {
    s match {
      case SCons(_, tfun) => tfun fmatch[BigInt, Boolean] {
          case n if tfun.is(() => repeat(n)) => true
          case _ => false
        }  
      case _              => true
    }
  }
  
  def nthElemInRepeat(n: BigInt, s: LList): BigInt = {
    require(n >= 0 && repeatStream(s))
    s match {
      case SNil() => BigInt(0)
      case s @ SCons(x, _) =>
        if (n == 0) x
        else nthElemInRepeat(n - 1, s.tailOrNil)
    }
  } ensuring (_ => alloc <= ? * n + ?)
  
  def takeWhileClient(n: BigInt) = {
    require(n >= 0)
    nthElemAfterTakeWhile(n,takeWhile(constFun2, natsFromn(0)))
  } 
  
  @inline
  def takeWhileStream(s: LList) = {
    s match {
      case SCons(_, tfun) => tfun fmatch[BigInt => Boolean, LList, Boolean] {
          case (p, l) if tfun.is(() => takeWhileSusp(p, l)) => true
          case _ => false
        }  
      case _              => true
    }
  }

  def nthElemAfterTakeWhile(n: BigInt, s: LList): BigInt  = {
    require(n >= 0 && takeWhileStream(s))
    s match {
      case SNil() => BigInt(0)
      case s @ SCons(x, _) =>
        if (n == 0) x
        else nthElemAfterTakeWhile(n - 1, s.tailOrNil)
    }
  } ensuring (_ => alloc <= ? * n + ?) 

  def scanClient(n: BigInt) = {
    require(n >= 0)
    nthElemAfterScan(n, scan(constFun3, BigInt(0), natsFromn(0)))
  }
  
  @inline
  def scanStream(s: LList) = {
    s match {
      case SCons(_, tfun) => tfun fmatch[(BigInt, BigInt) => BigInt, BigInt, LList, Boolean] {
          case (acc, z, l) if tfun.is(() => scanSusp(acc, z, l)) => true
          case _ => false
        }  
      case _              => true
    }
  }
  
  def nthElemAfterScan(n: BigInt, s: LList): BigInt  = {
    require(n >= 0 && scanStream(s))
    s match {
      case SNil() => BigInt(0)
      case s @ SCons(x, _) =>
        if (n == 0) x
        else nthElemAfterScan(n - 1, s.tailOrNil)
    }
  } ensuring (_ => alloc <= ? * n + ?) 
  
  def unfoldClient(n: BigInt, c: BigInt) = {
    require(n >= 0)
    nthElemAfterUnfold(n, unfold(constFun4, c))
  } ensuring (_ => alloc <= ? * n + ?) 

  @inline
  def unfoldStream(s: LList) = {
    s match {
      case SCons(_, tfun) => tfun fmatch[BigInt => (BigInt, BigInt), BigInt, Boolean] {
          case (f, n) if tfun.is(() => unfold(f, n)) => true
          case _ => false
        }  
      case _              => true
    }
  }
  def nthElemAfterUnfold(n: BigInt, s: LList): BigInt  = {
    require(n >= 0 && unfoldStream(s))
    s match {
      case SNil() => BigInt(0)
      case s @ SCons(x, _) =>
        if (n == 0) x
        else nthElemAfterUnfold(n - 1, s.tailOrNil)
    }
  } ensuring (_ => alloc <= ? * n + ?)

  def zipWithClient(n: BigInt) = {
    require(n >= 0)
    nthElemAfterZipWith(n, zipWith(constFun3, natsFromn(0), natsFromn(0)))
  }
  
  @inline
  def zipWithStream(s: LList) = {
    s match {
      case SCons(_, tfun) => tfun fmatch[(BigInt, BigInt) => BigInt, LList, LList, Boolean] {
          case (f, l1, l2) if tfun.is(() => zipWithSusp(f, l1, l2)) => true
          case _ => false
        }  
      case _              => true
    }
  }
  
  def nthElemAfterZipWith(n: BigInt, s: LList): BigInt  = {
    require(n >= 0 && zipWithStream(s))
    s match {
      case SNil() => BigInt(0)
      case s @ SCons(x, _) =>
        if (n == 0) x
        else nthElemAfterZipWith(n - 1, s.tailOrNil)
    }
  } ensuring (_ => alloc <= ? * n + ?) 
  
}
