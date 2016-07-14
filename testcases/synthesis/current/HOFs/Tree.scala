import leon.lang._
import leon.lang.synthesis._

object HOFDecomp1 {
  abstract class Tree[T] {
    def map[B](f: T => B): Tree[B] = {
      this match {
        case Node(v, l, r) => Node(f(v), l.map(f), r.map(f))
        case Leaf() => Leaf()
      }
    }

    def fold[B](z: B)(f: (T, B, B) => B): B = {
      this match {
        case Node(v, l, r) => f(v, l.fold(z)(f), r.fold(z)(f))
        case Leaf() => z
      }
    }
  }

  case class Node[T](v: T, l: Tree[T], r: Tree[T]) extends Tree[T]
  case class Leaf[T]() extends Tree[T]

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

    def ++(l: List[T]): List[T] = {
      this match {
        case Cons(h, t) => Cons(h, t ++ l)
        case Nil() => l
      }
    }
  }

  case class Cons[T](h: T, t: List[T]) extends List[T]
  case class Nil[T]() extends List[T]

  def countLeaves(in: Tree[Int]): Int = {
    // in.fold(1){ (v,l,r) => l+r }
    ???[Int]
  } ensuring {
    out => (in, out) passes {
      case Leaf() => 1
      case Node(13, Leaf(), Leaf()) => 2
      case Node(13, Leaf(), Node(13, Leaf(), Leaf())) => 3
      case Node(13, Node(13, Leaf(), Leaf()), Node(13, Leaf(), Node(13, Leaf(), Leaf()))) => 5
    }
  }

  def countNodes(in: Tree[Int]): Int = {
    // in.fold(0){ (v,l,r) => 1+l+r }
    ???[Int]
  } ensuring {
    out => (in, out) passes {
      case Leaf() => 0
      case Node(13, Leaf(), Leaf()) => 1
      case Node(13, Leaf(), Node(13, Leaf(), Leaf())) => 2
      case Node(13, Node(13, Leaf(), Leaf()), Node(13, Leaf(), Node(13, Leaf(), Leaf()))) => 4
    }
  }

  def flatten(in: Tree[Int]): List[Int] = {
    // in.fold(Nil) { (v, l, r) => Cons(v, Nil) ++ l ++ r }
    ???[List[Int]]
  } ensuring {
    out => (in, out) passes {
      case Leaf() => Nil[Int]()
      case Node(13, Leaf(), Leaf()) => Cons(13, Nil())
      case Node(12, Leaf(), Node(13, Leaf(), Leaf())) => Cons(12, Cons(13, Nil()))
      case Node(12, Node(13, Leaf(), Leaf()), Leaf()) => Cons(12, Cons(13, Nil()))
      case Node(12, Node(13, Leaf(), Leaf()), Node(12, Leaf(), Node(13, Leaf(), Leaf()))) => Cons(12, Cons(13, Cons(12, Cons(13, Nil()))))
    }
  }

  def max(a: Int, b: Int): Int = {
    if (a > b) a else b
  }

  def height(in: Tree[Int]): Int = {
    // in.fold(0) { (v, l, r) => 1+max(l, r) }
    ???[Int]
  } ensuring {
    out => (in, out) passes {
      case Leaf() => 0
      case Node(13, Leaf(), Leaf()) => 1
      case Node(13, Leaf(), Node(13, Leaf(), Leaf())) => 2
      case Node(13, Node(13, Leaf(), Leaf()), Leaf()) => 2
      case Node(13, Node(13, Leaf(), Leaf()), Node(13, Leaf(), Node(13, Leaf(), Leaf()))) => 3
    }
  }

  def incr(in: Tree[Int]): Tree[Int] = {
    // in.map{ _ + 1 }
    ???[Tree[Int]]
  } ensuring {
    out => (in, out) passes {
      case Leaf() => Leaf()
      case Node(13, Leaf(), Leaf()) => Node(14, Leaf(), Leaf())
      case Node(-4, Leaf(), Node(13, Leaf(), Leaf())) => Node(-3, Leaf(), Node(14, Leaf(), Leaf()))
      case Node(10, Node(11, Leaf(), Leaf()), Leaf()) => Node(11, Node(12, Leaf(), Leaf()), Leaf())
    }
  }

  def maxt(in: Tree[Int]): Int = {
    require(in != Leaf[Int]())
    // in.fold(in.v) { (v, l, r) => max(v, max(l, r)) }
    ???[Int]
  } ensuring {
    out => (in, out) passes {
      case Node(13, Leaf(), Leaf())                   => 13
      case Node(11, Leaf(), Leaf())                   => 11
      case Node(-4, Leaf(), Node(13, Leaf(), Leaf())) => 13
      case Node(16, Leaf(), Node(11, Leaf(), Leaf())) => 16
      case Node(9,  Node(11, Leaf(), Leaf()), Leaf()) => 11
      case Node(12, Node(13, Leaf(), Leaf()), Leaf()) => 13
      case Node(12, Node(13, Leaf(), Leaf()), Node(11, Leaf(), Leaf())) => 13
    }
  }

  def member(in: Tree[Int], v: Int): Boolean = {
    // in.fold(false) { (v2, l, r) => v == v2 || l || r  }
    ???[Boolean]
  } ensuring {
    out => ((in, v), out) passes {
      case (Leaf(), 10)                                     => false
      case (Node(10, Leaf(), Leaf()), 10)                   => true
      case (Node(11, Leaf(), Leaf()), 10)                   => false
      case (Node(9, Leaf(), Leaf()), 10)                    => false
      case (Node(11, Node(10, Leaf(), Leaf()), Leaf()), 10) => true
      case (Node(11, Leaf(), Node(10, Leaf(), Leaf())), 10) => true
      case (Node(11, Node(12, Leaf(), Leaf()), Leaf()), 10) => false
      case (Node(11, Leaf(), Node(12, Leaf(), Leaf())), 10) => false
    }
  }
}
