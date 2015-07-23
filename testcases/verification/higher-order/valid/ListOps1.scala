import leon._
import leon.lang._
import leon.annotation._
import leon.collection._


object ListOps1 {

  /**
   *    * Simple List operations
   *       **/

  def partition[A](f: A => Boolean, l: List[A]): (List[A], List[A]) = {
    l match {
      case Cons(h, t) => 
        val (h1, h2) = if (f(h)) (Cons(h, Nil()), Nil[A]())
        else (Nil[A](), Cons(h, Nil())) 
        val (t1, t2) = partition(f, t)
        (h1 ++ t1, h2 ++ t2)
      case Nil() => (Nil[A](), Nil[A]())
    }
  } ensuring { x: (List[A], List[A]) => x match {
    case (a, b) => a.forall(f) && 
    b.forall(x => !f(x)) && 
    a.size + b.size == l.size && 
    a.content ++ b.content == l.content
  }}

  def collect[A, B](f: A => Option[B], l: List[A]): List[B] = {
    l match {
      case Cons(h, t) =>
        f(h) match {
          case Some(b) => Cons(b, collect(f, t))
          case None()  => collect(f, t) 
        }
          case Nil() => Nil[B]()
    }
  } ensuring { 
    res => res.size <= l.size
  }

  def collectFirst[A, B](f: A => Option[B], l: List[A]): Option[B] = {
    l match {
      case Cons(h, t) =>
        f(h).orElse(collectFirst(f, t))
      case Nil() => None[B]()
    }
  } ensuring { 
    res => !l.isEmpty || res.isEmpty
  }


  def count[A](f: A => Boolean, l: List[A]): Int = {
    l match {
      case Cons(h, t) =>
        (if (f(h)) 1 else 0) + count(f, t)
      case Nil() => 0
    }
  } ensuring { 
    res => !(res > 0) || !l.isEmpty
  }

  def dropWhile[A](f: A => Boolean, l: List[A]): List[A] = {
    l match {
      case Cons(h, t) if  f(h) => dropWhile(f, t)
      case Cons(h, t) if !f(h) => l
      case Nil() => Nil[A]()
    }
  } ensuring { 
    res => 
      if(res.size < l.size) {
        f(l.head)
      } else {
        l.isEmpty || !f(l.head)
      }
  }

  def forall[A](f: A => Boolean, l: List[A]): Boolean = {
    l match {
      case Cons(h, t) if f(h) => forall(f, t)
      case Cons(_, t) => false
      case Nil() => true
    }
  } ensuring {
    res => res == !exists[A]({ x => !f(x) }, l)
  }

  def exists[A](f: A => Boolean, l: List[A]): Boolean = {
    l match {
      case Cons(h, t) if f(h) => true
      case Cons(_, t) => exists(f, t)
      case Nil() => false
    }
  } ensuring {
    res => res == res
  }


  /**
   *    * Map with universal quantifier in post as a witness argument
   *       **/

  def mapWitness[A,B](f: A => B, l: List[A], w: A): List[B] = {
    l match {
      case Cons(h, t) => f(h) :: mapWitness(f, t, w)
      case Nil() => Nil[B]()
    }
  } ensuring {
    res => if (l.content contains w) res.content contains f(w) else true
  }
}
