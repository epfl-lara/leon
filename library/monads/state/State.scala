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

@library
object ExampleCounter {

  import State._

  def counter(init: BigInt) = {

    @inline
    @library
    def tick = modify[BigInt](_ + 1)

    init >:: (for {
      _ <- tick
      _ <- tick
      _ <- tick
      r <- get
    } yield r)

  } ensuring( _ == init + 3 )
}

@library
object ExampleTicTacToe {

  import State._

  abstract class Square
  case object UL extends Square
  case object U  extends Square
  case object UR extends Square
  case object L  extends Square
  case object C  extends Square
  case object R  extends Square
  case object DL extends Square
  case object D  extends Square
  case object DR extends Square

  @inline
  val winningSets: List[Set[Square]] = List(
    Set(UL, U, UR),
    Set( L, C,  R),
    Set(DL, D, DR),
    Set(UL, L, DL),
    Set( U, C,  D),
    Set(UR, R, DR),
    Set(UR, C, DL),
    Set(UL, C, DR)
  )

  @inline
  def wins(sqs: Set[Square]) = winningSets exists { _ subsetOf sqs}

  case class Board(xs: Set[Square], os: Set[Square])
  case class TState(b: Board, xHasMove: Boolean) // true = X, false = O

  @inline
  val init = TState(Board(Set.empty[Square], Set.empty[Square]), true)

  @inline
  def legalMove(b: Board, sq: Square) = !(b.xs ++ b.os).contains(sq)

  @inline
  def move(sq: Square): State[TState, Unit] = {
    modify[TState] { case TState(board, xHasMove) =>
      TState(
        if (xHasMove)
          Board(board.xs ++ Set(sq), board.os)
        else
          Board(board.xs, board.os ++ Set(sq)),
        if (legalMove(board, sq))
          !xHasMove
        else
          xHasMove
      )
    }
  }

  @inline
  def play(moves: List[Square]): Option[Boolean] = {
    val b = foldLeftM_ (move, moves).exec(init).b
    if (wins(b.xs)) Some(true)
    else if (wins(b.os)) Some(false)
    else None[Boolean]()
  }

  //def ex = {
  //  play(List(UL, UR, C, D, DR)) == Some(true)
  //}.holds

  //def gameEnds(moves: List[Square], oneMore: Square) = {
  //  val res1 = play(moves)
  //  val res2 = play(moves :+ oneMore)
  //  res1.isDefined ==> (res1 == res2)
  //}.holds
}

@library
object ExampleFreshen {

  import State._
  import leon.lang.string._

  case class Id(name: String, id: BigInt)

  abstract class Expr
  case class EVar(id: Id) extends Expr
  case class EAbs(v: Id, body: Expr) extends Expr
  case class EApp(f: Expr, arg: Expr) extends Expr

  case class EState(counters: Map[String, BigInt])

  def addVar(name: String): State[EState, Id] = for {
    s <- get[EState]
    newId = if (s.counters.contains(name)) s.counters(name) + 1 else BigInt(0)
    _ <- put( EState(s.counters + (name -> newId) ) )
  } yield Id(name, newId)

  def freshen(e: Expr): State[EState, Expr] = e match {
    case EVar(Id(name, id)) =>
      for {
        s <- get
      } yield {
        val newId = if (s.counters.contains(name)) s.counters(name) else id
        EVar(Id(name, newId))
      }
    case EAbs(v, body) =>
      for {
        v2    <- addVar(v.name)
        body2 <- freshen(body)
      } yield EAbs(v2, body2)
    case EApp(f, arg) =>
      for {
        // We need to freshen both f and arg with the initial state,
        // so we save it here
        init <- get
        f2   <- freshen(f)
        _    <- put(init)
        arg2 <- freshen(arg)
      } yield EApp(f2, arg2)
  }

  val empty = EState(Map[String, BigInt]())

  def freshenNames(e: Expr): Expr = empty >:: freshen(e)

}

@library
object ExampleStackEval {

  import State._

  abstract class Expr
  case class Plus(e1: Expr, e2: Expr) extends Expr
  case class Minus(e1: Expr, e2: Expr) extends Expr
  case class UMinus(e: Expr) extends Expr
  case class Lit(i: BigInt) extends Expr

  def push(i: BigInt) = State[List[BigInt], Unit]( s => ( (), i :: s) )
  def pop: State[List[BigInt], BigInt] = for {
    l <- get
    _ <- put(l.tailOption.getOrElse(Nil[BigInt]()))
  } yield l.headOption.getOrElse(0)


  def evalM(e: Expr): State[List[BigInt], Unit] = e match {
    case Plus(e1, e2) =>
      for {
        _ <- evalM(e1)
        _ <- evalM(e2)
        i2 <- pop
        i1 <- pop
        _ <- push(i1 + i2)
      } yield(())
    case Minus(e1, e2) =>
      for {
        _ <- evalM(e1)
        _ <- evalM(e2)
        i2 <- pop
        i1 <- pop
        _ <- push(i1 - i2)
      } yield(())
    case UMinus(e) =>
      evalM(e) >> pop >>= (i => push(-i))
    case Lit(i) =>
      push(i)
  }

  def eval(e: Expr): BigInt = e match {
    case Plus(e1, e2) =>
      eval(e1) + eval(e2)
    case Minus(e1, e2) =>
      eval(e1) - eval(e2)
    case UMinus(e) =>
      -eval(e)
    case Lit(i) =>
      i
  }

  def empty = List[BigInt]()

  //def evalVsEval(e: Expr) = {
  //  evalM(e).exec(empty).head == eval(e)
  //}.holds

}
