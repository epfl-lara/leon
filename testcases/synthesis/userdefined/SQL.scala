import leon.lang._
import leon.lang.synthesis._
import leon.annotation.grammar._
import leon.grammar._

import Grammar1._

object Grammar1 {

  case class Person(id: Int, idJob: Int, name: String, age: Int)
  case class Job(id: Int, name: String)

  abstract class List[T] {
    def size: BigInt = {
      this match {
        case Cons(h, t) => t.size + 1
        case Nil() => BigInt(0)
      }
    } ensuring { _ >= 0 }

    def filter(f: T => Boolean): List[T] = {
      this match {
        case Cons(h, t) =>
          if (f(h)) {
            Cons(h, t.filter(f))
          } else {
            t.filter(f)
          }

        case Nil() =>
          Nil()
      }
    }

    def withFilter(f: T => Boolean) = filter(f)

    def map[U](f: T => U): List[U] = {
      this match {
        case Cons(h, t) =>
          Cons(f(h), t.map(f))
        case Nil() =>
          Nil()
      }
    }

    def flatMap[U](f: T => List[U]): List[U] = {
      this match {
        case Cons(h, t) =>
          f(h) ++ t.flatMap(f)
        case Nil() =>
          Nil()
      }
    }

    def ++(that: List[T]): List[T] = {
      this match {
        case Nil() =>
          that
        case Cons(h, t) =>
          Cons(h, (t ++ that))
      }
    }
  }



  case class Cons[T](h: T, t: List[T]) extends List[T]
  case class Nil[T]() extends List[T]

  @production
  def filter[T](t: List[T])(where: T => Boolean): List[T] = SQL.filter(t)(where)

  @production
  def select[T, U](t: List[T])(f: T => U): List[U] = SQL.select(t)(f)

  @production
  def join[T, U](t1: List[T], t2: List[U])(on: (T, U) => Boolean): List[(T, U)] = SQL.join(t1, t2)(on)

  @production
  def gt(i1: Int, i2: Int) = i1 > i2

  @production
  def ge(i1: Int, i2: Int) = i1 >= i2

  @production
  def lt(i1: Int, i2: Int) = i1 < i2

  @production
  def le(i1: Int, i2: Int) = i1 <= i2

  @production
  def personName(p: Person) = p.name

  @production
  def personAge(p: Person) = p.age

  @production
  def thisdoesntmatter[A]: A = variable[A]
}

object SQL {
  def filter[T](t: List[T])(where: T => Boolean): List[T] = {
    for {
      r <- t if where(r)
    } yield {
      r
    }
  }

  def select[T, U](t: List[T])(f: T => U): List[U] = {
    for {
      r <- t
    } yield {
      f(r)
    }
  }

  def join[T, U](t1: List[T], t2: List[U])(on: (T, U) => Boolean): List[(T, U)] = {
    for {
      r1 <- t1
      r2 <- t2 if on(r1, r2)
    } yield {
      (r1, r2)
    }
  }
}

object Test1 {
  def persons: List[Person] = {
    Cons(Person(1, 6, "Manos",   18),
    Cons(Person(2, 4, "Ravi",    19),
    Cons(Person(3, 4, "Regis",   12),
    Cons(Person(4, 3, "Nicolas", 21),
    Cons(Person(5, 1, "Georg",   22),
    Cons(Person(6, 2, "Mukund",  55),
    Nil()))))))
  }

  def jobs: List[Job] = {
    Cons(Job(1, "Sales"),
    Cons(Job(2, "Cashier"),
    Cons(Job(3, "Waiter"),
    Cons(Job(4, "Surgeon"),
    Cons(Job(5, "Military"),
    Cons(Job(6, "Architect"),
    Nil()))))))
  }

  /*
  def personNames(implicit ps: List[Person], js: List[Job]) = {
   ???[List[String]]

   // select(
   //   ps
   // )(_.name)

  } ensuring { (res: List[String]) =>
    ((ps, js), res) passes {
      case (ps, js) if ps == persons && js == jobs =>
        Cons("Manos", Cons("Ravi", Cons("Regis", Cons("Nicolas", Cons("Georg", Cons("Mukund", Nil()))))))
    }
  }
  */

  def personsOlderThan(age: Int)(implicit ps: List[Person], js: List[Job]) = {
   ???[List[String]]

   // select(
   //   filter(
   //     ps
   //   )(p => p.age > age)
   // )(_.name)

  } ensuring { (res: List[String]) =>
    ((age, ps, js), res) passes {
      case (30, ps, js) if ps == persons && js == jobs =>
        Cons("Mukund", Nil())

      case (20, ps, js) if ps == persons && js == jobs =>
        Cons("Nicolas", Cons("Georg", Cons("Mukund", Nil())))

      case (18, ps, js) if ps == persons && js == jobs =>
        Cons("Ravi", Cons("Nicolas", Cons("Georg", Cons("Mukund", Nil()))))
    }
  }

  /*
  def personsOfJob(j: String)(implicit ps: List[Person], js: List[Job]) = {
   //???[List[String]]

    select(
      filter(
        join(ps, js)((p, j) => p.idJob == j.id)
      )(pj => pj._2.name == j)
    )(_._1.name)

  } ensuring { (res: List[String]) =>
    ((j, ps, js), res) passes {
      case ("Sales",    ps, js) if ps == persons && js == jobs =>
        Cons("Georg", Nil())

      case ("Military", ps, js) if ps == persons && js == jobs =>
        Nil();

      case ("Surgeon",  ps, js) if ps == persons && js == jobs =>
        Cons("Ravi", Cons("Regis", Nil()))

    }
  }
  */

}
