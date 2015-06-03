/*
A very much simplified implementation of the types in the
Dependent Object Calculus (http://lampwww.epfl.ch/~amin/dot/fool.pdf).

It's interesting because expansion calls itself recursively (through
lookupInVar), and passes the results of this recursive call to another
recursive call.

The termination checker loops forever [or at least longer than several
minutes ;-)] on this case.
*/

import leon.lang._
import leon.collection._
import leon._

object lambdaDot {
  abstract class Label
  case class TypLabel(id: BigInt) extends Label
  case class MtdLabel(id: BigInt) extends Label

  abstract class Type
  case class Top() extends Type
  case class Bot() extends Type
  case class Rcd(ds: List[Dec]) extends Type
  case class TSel(x: BigInt, l: BigInt) extends Type
  
  abstract class Dec {
    def label: Label = this match {
      case TDec(l, _, _) => TypLabel(l)
      case MDec(m, _, _) => MtdLabel(m)
    }
  }
  case class TDec(l: BigInt, lowerBound: Type, upperBound: Type) extends Dec
  case class MDec(m: BigInt, argType: Type, retType: Type) extends Dec

  abstract class Decs
  case class FiniteDecs(l: List[Dec]) extends Decs
  case class BotDecs() extends Decs
  
  def lookupInEnv(x: BigInt, env: List[(BigInt, Type)]): Option[Type] = env match {
    case Cons((y, t), rest) => if (x == y) Some(t) else lookupInEnv(x, rest)
    case Nil() => None()
  }
  
  def lookupInDecList(name: Label, l: List[Dec]): Option[Dec] = (l match {
    case Cons(d, ds) => if (d.label == name) Some(d) else lookupInDecList(name, ds)
    case Nil() => None()
  }) ensuring { res => res match {
    case Some(d) => d.label == name
    case None() => true
  }}
  
  def lookupInDecs(name: Label, l: Decs): Option[Dec] = (l match {
    case FiniteDecs(l) => lookupInDecList(name, l)
    case BotDecs() => name match {
      case TypLabel(l) => Some(TDec(l, Top(), Bot()))
      case MtdLabel(m) => Some(MDec(m, Top(), Bot()))
    }
  }) ensuring { res => res match {
    case Some(d) => d.label == name
    case None() => true
  }}

  def wfType(env: List[(BigInt, Type)], t: Type, shallow: Boolean): Boolean = t match {
    case Top() => true
    case Bot() => true
    case Rcd(ds) => shallow || wfDecList(env, ds)
    case TSel(x, l) => lookupInVar(env, x, TypLabel(l)) match {
      case Some(TDec(l, lo, hi)) => wfType(env, lo, true) && wfType(env, hi, true)
      case None() => false
    }
  }
  
  def wfDec(env: List[(BigInt, Type)], d: Dec): Boolean = d match {
    case TDec(l, lo, hi) => wfType(env, lo, false) && wfType(env, hi, false)
    case MDec(m, a, r) => wfType(env, a, false) && wfType(env, r, false)
  }
  
  def wfDecList(env: List[(BigInt, Type)], ds: List[Dec]): Boolean = ds match {
    case Cons(d, ds) => wfDec(env, d) && wfDecList(env, ds)
    case Nil() => true
  }

  def expansion(env: List[(BigInt, Type)], t: Type): Option[Decs] = {
    //require(wfType(env, t, false))
    t match {
      case Top() => Some(FiniteDecs(Nil()))
      case Bot() => Some(FiniteDecs(Nil()))
      case Rcd(ds) => Some(FiniteDecs(ds))
      case TSel(x, l) => lookupInVar(env, x, TypLabel(l)) match {
        case Some(TDec(l, lo, hi)) => expansion(env, hi)
        case None() => None()
      }
    }
  }
  
  def lookupInVar(env: List[(BigInt, Type)], x: BigInt, l: Label): Option[Dec] = {
    lookupInEnv(x, env) match {
      case Some(tx) => expansion(env, tx) match {
        case Some(dsx) => lookupInDecs(l, dsx)
        case None() => None()
      }
      case None() => None()
    }
  } ensuring { res => res match {
    case Some(d) => d.label == l
    case None() => true
  }}
  
}

