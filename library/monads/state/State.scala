package leon.monads.state

import leon.collection._
import leon.lang._
import leon.annotation._

@library
case class State[S, A](runState: S => (A, S)) {

  /** Basic monadic methods */

  // Monadic bind
  @inline
  def flatMap[B](f: A => State[S, B]): State[S, B] = {
    State { s =>
      val (a, newS) = runState(s)
      f(a).runState(newS)
    }
  }

  // All monads are also functors, and they define the map function
  @inline
  def map[B](f: A => B): State[S, B] = {
    State { s =>
      val (a, newS) = runState(s)
      (f(a), newS)
    }
  }

  @inline
  def >>=[B](f: A => State[S, B]): State[S, B] = flatMap(f)

  @inline
  def >>[B](that: State[S, B]) = >>= ( _ => that )

  @inline
  // This is unfortunate, but implementing properly would just lead to an error
  def withFilter(f: A => Boolean): State[S, A] = this

  @inline
  def eval(s: S) = runState(s)._1
  @inline
  def exec(s: S) = runState(s)._2

  // eval with arguments flipped
  @inline
  def >:: (s: S) = eval(s)

  /** Helpers */
  @isabelle.noBody
  def forever[B]: State[S, B] = this >> forever

  def apply(s: S) = runState(s)

}

@library
object State {

  @inline
  def get[A]: State[A, A] = State( a => (a, a) )

  @inline
  def gets[S, A](f: S => A): State[S, A] = for {
    s <- get[S]
  } yield f(s)

  @inline
  def put[S](s: S): State[S, Unit] = State { _ => ((), s) }

  @inline
  def modify[S](f: S => S): State[S, Unit] = for {
    s <- get[S]
    s2 <- put(f(s))
  } yield s2

  // Monadic unit
  @inline
  def unit[S, A](a: A): State[S, A] = State { s => (a, s) }

  @inline
  def state[S]: State[S, S] = State(s => (s, s))

  @inline
  // Left-to-right Kleisli composition of monads
  def >=>[S, A, B, C](f: A => State[S, B], g: B => State[S, C], a: A): State[S, C] = {
    for {
      b <- f(a)
      c <- g(b)
    } yield c
  }

  /* Monadic-List functions */

  def mapM[A, B, S](f: A => State[S, B], l: List[A]): State[S, List[B]] = {
    l match {
      case Nil() => unit(Nil[B]())
      case Cons(x, xs) => for {
        mx <- f(x)
        mxs <- mapM(f,xs)
      } yield mx :: mxs
    }
  }

  def mapM_ [A, B, S] (f: A => State[S, B], l: List[A]): State[S, Unit] = {
    l match {
      case Nil() => unit(())
      case Cons(x, xs) => for {
        mx <- f(x)
        mxs <- mapM_ (f, xs)
      } yield ()
    }
  }

  def sequence[S, A](l: List[State[S, A]]): State[S, List[A]] = {
    l.foldRight[State[S, List[A]]](unit(Nil[A]())){
      case (x, xs) => for {
        v <- x
        vs <- xs
      } yield v :: vs
    }
  }

  def filterM[S, A](f: A => State[S, Boolean], l: List[A]): State[S, List[A]] = {
    l match {
      case Nil() => unit(Nil[A]())
      case Cons(x, xs) => for {
        flg <- f(x)
        rest <- filterM(f, xs)
      } yield (if (flg) x :: rest else rest)
    }
  }

  //(b -> a -> m b) -> b -> t a -> m b
  def foldLeftM[S, A, B](f: (B, A) => State[S, B], z: B, l: List[A]): State[S, B] = {
    l match {
      case Nil() => unit(z)
      case Cons(x, xs) =>
        f(z, x) >>= ( z0 => foldLeftM(f,z0,xs) )
    }
  }

  //(b -> a -> m b) -> b -> t a -> m ()
  def foldLeftM_ [S, A](f: A => State[S, Unit], l: List[A]): State[S, Unit] = {
    l match {
      case Nil() => unit(())
      case Cons(x, xs) =>
        f(x) >> foldLeftM_ (f, xs)
    }
  }

}

@library
object MonadStateLaws {
  import State._

  /* Monadic laws:
   *
   * return a >>= k  =  k a
   * m >>= return  =  m
   * m >>= (x -> k x >>= h)  =  (m >>= k) >>= h
   *
   * Note: We cannot compare State's directly because State contains an anonymous function.
   * So we have to run them on an initial state.
   */

  def unitLeftId[A, B, S](a: A, k: A => State[S, B])(s: S): Boolean = {
    (unit(a) >>= (k))(s) == k(a)(s)
  }.holds

  def unitRightId[S, A](m: State[S,A])(s:S): Boolean = {
    (m >>= unit).runState(s) == m.runState(s)
  }.holds

  def assoc[S, A, B, C](m: State[S,A], k: A => State[S, B], h: B => State[S, C])(s: S) = {
    (m >>= (x => k(x) >>= h)).runState(s) == (m >>= k >>= h).runState(s)
  }.holds

  /* This is the same as assoc, but proves in 42sec instead of 50ms!
  def assoc2[S, A, B, C](m: State[S,A], k: A => State[S, B], h: B => State[S, C])(s: S) = {
    val lhs = for {
      x <- m
      y <- for {
        z <- k(x)
        w <- h(z)
      } yield w
    } yield y

    val rhs = for {
      x <- m
      y <- k(x)
      z <- h(y)
    } yield z

    lhs.runState(s) == rhs.runState(s)
  }.holds
  */


  /* The law connecting monad and functor instances:
   *
   * m >>= (return . f)  =  m map f
   */

  def mapToFlatMap[S, A, B](m: State[S, A], f: A => B)(s: S): Boolean = {
    (m >>= (x => unit(f(x)))).runState(s) == (m map f).runState(s)
  }.holds


  /* Different theorems */

  //@induct
  //def mapMVsSequenceM[S, A, B](f: A => State[S, B], l: List[A])(s: S) = {
  //  mapM(f, l).runState(s) == sequence(l map f).runState(s)
  //}.holds


}
