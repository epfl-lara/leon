package cp

object Definitions {
  import Terms._

  class spec extends StaticAnnotation

  final class NotImplementedException extends Exception

  final class UnsatisfiableConstraintException extends Exception
  final class UnknownConstraintException extends Exception

  implicit def pred2cons1[A](pred : A => Boolean) : Constraint1[A] = throw new NotImplementedException
  implicit def pred2cons2[A,B](pred : (A,B) => Boolean) : Constraint2[A,B] = throw new NotImplementedException

  implicit def func2optFunc1[A](func : A => Int) : IntTerm1[A] = throw new NotImplementedException
  implicit def func2optFunc2[A,B](func : (A,B) => Int) : IntTerm2[A,B] = throw new NotImplementedException

  implicit def func2term1[T1,R](func : T1 => R) : Term1[T1,R] = throw new NotImplementedException
  implicit def func2term2[T1,T2,R](func : (T1,T2) => R) : Term2[T1,T2,R] = throw new NotImplementedException

  def distinct[A](args: A*) : Boolean = {
    args.toList.distinct.size == args.size
  }
}
