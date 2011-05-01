package cp

object Definitions {
  import Constraints._

  class spec extends StaticAnnotation

  final class NotImplementedException extends Exception

  final class UnsatisfiableConstraintException extends Exception
  final class UnknownConstraintException extends Exception

  implicit def pred2cons1[A](pred : A => Boolean) : Constraint1[A] = throw new NotImplementedException
  implicit def pred2cons2[A,B](pred : (A,B) => Boolean) : Constraint2[A,B] = throw new NotImplementedException

  implicit def func2optFunc1[A](func : A => Int) : OptimizingFunction1[A] = throw new NotImplementedException
  implicit def func2optFunc2[A,B](func : (A,B) => Int) : OptimizingFunction2[A,B] = throw new NotImplementedException

  def distinct[A](args: A*) : Boolean = {
    args.toList.distinct.size == args.size
  }
}
