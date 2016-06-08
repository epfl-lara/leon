import leon.lang._
import leon.lang.synthesis._

object HOFDecomp1 {

  abstract class List[T] {
    def filter(f: T => Boolean): List[T] = {
      this match {
        case Cons(h, t) =>
          if (f(h)) {
            Cons(h, t.filter(f))
          } else {
            t.filter(f)
          }

        case Nil() => Nil()
      }
    }

    def map[B](f: T => B): List[B] = {
      this match {
        case Cons(h, t) => Cons(f(h), t.map(f))
        case Nil()      => Nil[B]()
      }
    }

    def foldr[B](z: B)(f: (B, T) => B): B = {
      this match {
        case Cons(h, t) => f(t.foldr(z)(f), h)
        case Nil()      => z
      }
    }

    def foldl[B](z: B)(f: (B, T) => B): B = {
      this match {
        case Cons(h, t) => t.foldl(f(z, h))(f)
        case Nil()      => z
      }
    }

    def collect[B](f: T => Option[B]): List[B] = {
      this match {
        case Cons(h, t) => f(h) match {
          case Some(v) => Cons(v, t.collect(f))
          case None() => t.collect(f)
        }
        case Nil() => Nil[B]()
      }
    }
  }

  case class Cons[T](h: T, t: List[T]) extends List[T]
  case class Nil[T]() extends List[T]

  def add(in: List[Int], v: Int): List[Int] = {
    // in.map(_ + v)
    ???[List[Int]]
  } ensuring {
    out => ((in, v), out) passes {
      case (Nil(), 1)                                          => Nil()
      case (Cons(10, Nil()), 2)                                => Cons(12, Nil())
      case (Cons(12, Nil()), -2)                               => Cons(10, Nil())
      case (Cons(1, Cons(-2, Cons(3, Cons(-4, Nil())))), 1)    => Cons(2, Cons(-1, Cons(4, Cons(-3, Nil()))))
      case (Cons(1, Cons(1, Cons(1, Cons(1, Nil())))), 10)     => Cons(11, Cons(11, Cons(11, Cons(11, Nil()))))
    }
  }


  // TODO: Does not work because it requires in.foldr(Cons(v, Nil)) { Cons(_, _) }
  //                                                  ~~~~~~~~~~~~

  def append(in: List[Int], v: Int): List[Int] = {
    ???[List[Int]]
  } ensuring {
    out => ((in, v), out) passes {
      case (Nil(), 1)                   => Cons(1, Nil())
      case (Cons(0, Nil()), 1)          => Cons(0, Cons(1, Nil()))
      case (Cons(0, Nil()), 2)          => Cons(0, Cons(2, Nil()))
      case (Cons(0, Cons(1, Nil())), 2) => Cons(0, Cons(1, Cons(2, Nil())))
    }
  }

  def concat(in1: List[Int], in2: List[Int]): List[Int] = {
    //in1.foldr(in2) { (a, b) => Cons(b, a) }
    ???[List[Int]]
  } ensuring {
    out => ((in1, in2), out) passes {
      case (Nil(), Nil())                            => Nil()
      case (Cons(0, Nil()), Nil())                   => Cons(0, Nil())
      case (Cons(0, Nil()), Cons(1, Nil()))          => Cons(0, Cons(1, Nil()))
      case (Cons(0, Cons(2, Nil())), Cons(1, Nil())) => Cons(0, Cons(2, Cons(1, Nil())))
      case (Nil(), Cons(1, Cons(2, Nil())))          => Cons(1, Cons(2, Nil()))
    }
  }

  def duplicate(in: List[Int]): List[Int] = {
    //in.foldr[List[Int]](Nil()) { (a, b) => Cons(b, Cons(b, a)) }
    ???[List[Int]]
  } ensuring {
    out => (in, out) passes {
      case Nil()                            => Nil()
      case Cons(0, Nil())                   => Cons(0, Cons(0, Nil()))
      case Cons(2, Cons(0, Nil()))          => Cons(2, Cons(2, Cons(0, Cons(0, Nil()))))
      case Cons(1, Cons(1, Nil()))          => Cons(1, Cons(1, Cons(1, Cons(1, Nil()))))
    }
  }

  def isEven(x: Int): Boolean = {
    x % 2 == 0
  }

  def evens(in: List[Int]): List[Int] = {
    //in.filter(_ % 2 == 0)
    ???[List[Int]]
  } ensuring {
    out => (in, out) passes {
      case Nil()                            => Nil()
      case Cons(0, Nil())                   => Cons(0, Nil())
      case Cons(1, Cons(0, Nil()))          => Cons(0, Nil())
      case Cons(5, Cons(4, Cons(2, Nil()))) => Cons(4, Cons(2, Nil()))
    }
  }

  def last(in: List[Int]): Int = {
    require(in != Nil[Int]())
    //in.foldl(0){ (a, b) => b }
    ???[Int]
  } ensuring {
    out => (in, out) passes {
      case Cons(0, Nil())                   => 0
      case Cons(1, Cons(2, Nil()))          => 2
      case Cons(5, Cons(4, Cons(1, Nil()))) => 1
    }
  }

  def size(in: List[Int]): Int = {
    //in.foldl(0){ (a, b) => a+1 }
    ???[Int]
  } ensuring {
    out => (in, out) passes {
      case Nil()                            => 0
      case Cons(0, Nil())                   => 1
      case Cons(1, Cons(0, Nil()))          => 2
      case Cons(2, Cons(1, Cons(0, Nil()))) => 3
    }
  }

  def max(a: Int, b: Int): Int = {
    if (a > b) a else b
  }

  // TODO: requires' split first
  def max(in: List[Int]): Int = {
    require(in != Nil[Int]())
    //in.tail.foldl(in.head){ (a, b) => max(a,b) }
    ???[Int]
  } ensuring {
    out => (in, out) passes {
      case Cons(0, Nil())                   => 0
      case Cons(4, Cons(0, Nil()))          => 4
      case Cons(-1, Cons(0, Nil()))         => 0
      case Cons(5, Cons(0, Nil()))          => 5
      case Cons(1, Cons(5, Cons(0, Nil()))) => 5
    }
  }

  def member[T](in: List[T], v: T): Boolean = {
    //in.foldl(false){ (a, b) => b || a == v }
    ???[Boolean]
  } ensuring {
    out => ((in, v), out) passes {
      case (Nil(), t)                            => false
      case (Cons(a, Nil()), b)  if a != b        => false
      case (Cons(a, Nil()), b)  if a == b        => true
      case (Cons(a, Cons(a2, Nil())), b)  if a == b => true
      case (Cons(a, Cons(a2, Nil())), b)  if a2 == b => true
    }
  }

  def reverse(in: List[Int]): List[Int] = {
    ???[List[Int]]
  } ensuring {
    out => (in, out) passes {
      case Nil()                            => Nil()
      case Cons(0, Nil())                   => Cons(0, Nil())
      case Cons(1, Nil())                   => Cons(1, Nil())
      case Cons(2, Nil())                   => Cons(2, Nil())
      case Cons(0, Cons(1, Nil()))          => Cons(1, Cons(0, Nil()))
      case Cons(1, Cons(2, Nil()))          => Cons(2, Cons(1, Nil()))
      case Cons(0, Cons(1, Cons(2, Nil()))) => Cons(2, Cons(1, Cons(0, Nil())))
    }
  }

  def sum(in: List[Int]): Int = {
    // in.fold(0) { (a, b) => a + b }
    ???[Int]
  } ensuring {
    out => (in, out) passes {
      case Nil()                                         => 0
      case Cons(12, Nil())                               => 12
      case Cons(1, Cons(12, Nil()))                      => 13
      case Cons(1, Cons(-2, Cons(3, Cons(-4, Nil()))))   => -2
      case Cons(1, Cons(1, Cons(1, Cons(1, Nil()))))     => 4
    }
  }


  case class Person(name: String, age: Int)

  def adultsNames(in: List[Person]): List[String] = {
    // in.filter(_.age >= 18).map(_.name)
    //
    // in.collect { p =>
    //  if (p.age >= 18) Some(p.name) else None
    //}
    ???[List[String]]
  } ensuring {
    out => (in, out) passes {
      case Cons(Person(a, 18), Cons(Person(b, 19), Cons(Person(c, 42),  Cons(Person(d, 20),  Nil())))) => Cons(a, Cons(b, Cons(c, Cons(d, Nil()))))
      case Cons(Person(a, -5), Cons(Person(b, 19), Cons(Person(c, 17), Cons(Person(d, 18),  Nil()))))  => Cons(b, Cons(d, Nil()))
      case Cons(Person(a, -2), Cons(Person(b, 17), Cons(Person(c, 16), Cons(Person(d, 0), Nil()))))    => Nil()
      case Nil()                                                                                       => Nil()
    }
  }

  def posNames(in: List[Person]): List[String] = {
    // in.filter(_.age >= 0).map(_.name)
    //
    // in.collect { p =>
    //  if (p.age >= 0) Some(p.name) else None
    //}
    ???[List[String]]
  } ensuring {
    out => (in, out) passes {
      case Cons(Person(a, 0),  Cons(Person(b, 10), Cons(Person(c, 3),  Cons(Person(d, 5),  Nil())))) => Cons(a, Cons(b, Cons(c, Cons(d, Nil()))))
      case Cons(Person(a, -5), Cons(Person(b, 2),  Cons(Person(c, -2), Cons(Person(d, 3),  Nil())))) => Cons(b, Cons(d, Nil()))
      case Cons(Person(a, -2), Cons(Person(b, -1), Cons(Person(c, -3), Cons(Person(d, -2), Nil())))) => Nil()
      case Nil()                                                                                     => Nil()
    }
  }
}
