package stream

import leon._
import lang._
import annotation._
import instrumentation._
import mem._
import higherorder._
import collection._
import invariant._

object GenericStreamLibrary {

  // TODO: Can be converted to generic, 'transpose', 'unzip' can be done then
  /**
   * A placeholder in a stream is either a Val or a Susp()
   */
  sealed abstract class ValOrSusp[T] {
    // ideally, fval should not be called on `Val` as it would unnecessarily cache it.
    lazy val fval = {
      this match {
        case Susp(f) => f()
        case Val(x)  => x
      }
    }
  }
  case class Val[T](x: LList[T]) extends ValOrSusp[T]
  case class Susp[T](fun: () => LList[T]) extends ValOrSusp[T]

  /**
   *  An infinite integer stream.
   *  Technically, the data structure is *not* infinite but the tail has a higher-order function.
   */
  sealed abstract class LList[T] {
    //@inline
    def tail = {
      require(this != SNil[T]())
      val SCons(x, tailFun) = this
      tailFun match {
        case s @ Susp(f) => s.fval
        case Val(x)      => x
      }
    }

    def tailOrNil = {
      this match {
        case SNil() => this
        case SCons(x, tailFun) =>
          tailFun match {
            case s @ Susp(f) => s.fval
            case Val(x)      => x
          }
      }
    }

    // this will not modify state
    def tailVal = {
      require(this != SNil[T]())
      val SCons(x, tailFun) = this
      tailFun match {
        case s @ Susp(f) => s.fval*
        case Val(x)      => x
      }
    }

    //@inline
    def tailCached = {
      require(this != SNil[T]())
      val SCons(x, tailFun) = this
      tailFun match {
        case Val(_) => true
        case s      => s.fval.cached
      }
    }
  }
  case class SCons[T](x: T, tailFun: ValOrSusp[T]) extends LList[T]
  case class SNil[T]() extends LList[T]


  // TODO: Tryout the 'transpose' function
  /**
   * Apply a function uniformly over all elements of a sequence.
   */
  //   def map[U, T](f: U => T, s: LList[U]): LList[T] = {
  // //    /require(validNatStream(s))
  //     s match {
  //       case SNil()          => SNil()
  //       case l @ SCons(x, _) => SCons(f(x), Susp(() => mapSusp(f, s)))
  //     }
  //   } ensuring (_ => time <= ?)

  //   @invisibleBody
  //   def mapSusp[U, T](f: U => T, s: LList[U]) = {
  //     require(validNatStream(s))
  //     map(f, s.tailOrNil)
  //   } ensuring(_ => time <= ?)

  //   def head[T](fail: () => T, s: LList[T]): T = s match {
  //     case SNil() => fail()
  //     case SCons(x, _) => x
  //   }

  //   def tailOp[T](s: LList[T]) = s.tailOrNil

  //  def transpose[T](s: LList[LList[T]], fail: () => T): LList[LList[T]] = {
  //    s match {
  //      case SCons(SCons(x, xs), _) =>
  //        val hfun = (l: LList[T]) => head(fail, l)
  //        val tfun = (l: LList[T]) => l.tailOrNil
  //        val susp1 = Susp[LList[T]](() => transposeSusp(hfun, s))
  //        val susp2 = SCons[LList[T]](xs, Susp(() => transposeSusp(tfun, s)))
  //        SCons[LList[T]](SCons[T](x, susp1),
  //            Susp(() => transpose(susp2, fail)))
  //      case SNil() => s
  //    }
  //  }
  //
  //  def transposeSusp[T](f: LList[T] => T, s: LList[LList[T]]): LList[T] = {
  //    map(f, s.tailOrNil)
  //  }
}
