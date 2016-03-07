/* Copyright 2009-2016 EPFL, Lausanne */

object Overrides {

  abstract class A[T] {
    def x[A](a: A): (A,T)
  }

  abstract class B[R] extends A[R] {
    def x[B](b: B) = x(b)
  }

  case class C[W](c: W) extends B[W] {
    override def x[C](f: C) = (f,c)
  }

  case class D[Z]() extends B[Z]
}
