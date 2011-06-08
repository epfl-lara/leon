package cp

object Definitions {
  import Terms._
  import LTrees._

  class spec extends StaticAnnotation

  final class NotImplementedException extends Exception

  final class UnsatisfiableConstraintException extends Exception
  final class UnknownConstraintException extends Exception

  implicit def func2term1[T1,R](func : T1 => R) : Term1[T1,R] = throw new NotImplementedException
  implicit def func2term2[T1,T2,R](func : (T1,T2) => R) : Term2[T1,T2,R] = throw new NotImplementedException
  implicit def func2term3[T1,T2,T3,R](func : (T1,T2,T3) => R) : Term3[T1,T2,T3,R] = throw new NotImplementedException
  implicit def func2term4[T1,T2,T3,T4,R](func : (T1,T2,T3,T4) => R) : Term4[T1,T2,T3,T4,R] = throw new NotImplementedException
  implicit def func2term5[T1,T2,T3,T4,T5,R](func : (T1,T2,T3,T4,T5) => R) : Term5[T1,T2,T3,T4,T5,R] = throw new NotImplementedException
  implicit def func2term6[T1,T2,T3,T4,T5,T6,R](func : (T1,T2,T3,T4,T5,T6) => R) : Term6[T1,T2,T3,T4,T5,T6,R] = throw new NotImplementedException
  implicit def func2term7[T1,T2,T3,T4,T5,T6,T7,R](func : (T1,T2,T3,T4,T5,T6,T7) => R) : Term7[T1,T2,T3,T4,T5,T6,T7,R] = throw new NotImplementedException
  implicit def func2term8[T1,T2,T3,T4,T5,T6,T7,T8,R](func : (T1,T2,T3,T4,T5,T6,T7,T8) => R) : Term8[T1,T2,T3,T4,T5,T6,T7,T8,R] = throw new NotImplementedException
  implicit def func2term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,R](func : (T1,T2,T3,T4,T5,T6,T7,T8,T9) => R) : Term9[T1,T2,T3,T4,T5,T6,T7,T8,T9,R] = throw new NotImplementedException

  implicit def int2lexpr(i: Int): LIntLiteral = LIntLiteral(i)
  implicit def boolean2lexpr(b: Boolean): LBooleanLiteral = LBooleanLiteral(b)

  def distinct[A](args: A*) : Boolean = {
    args.toList.distinct.size == args.size
  }
}
