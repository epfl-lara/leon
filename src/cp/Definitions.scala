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

  implicit def force[T](l : L[T]): T = {
    l.value
  }

  implicit def forceLTuple[T](ltuple: LTuple[T]): T = ltuple.value

  implicit def ltuple2tuple1[T1](ltuple: LTuple1[T1]): L[T1] = ltuple._1
  implicit def ltuple2tuple2[T1,T2](ltuple: LTuple2[T1,T2]): (L[T1],L[T2]) = (ltuple._1,ltuple._2)
  implicit def ltuple2tuple3[T1,T2,T3](ltuple: LTuple3[T1,T2,T3]): (L[T1],L[T2],L[T3]) = (ltuple._1,ltuple._2,ltuple._3)
  implicit def ltuple2tuple4[T1,T2,T3,T4](ltuple: LTuple4[T1,T2,T3,T4]): (L[T1],L[T2],L[T3],L[T4]) = (ltuple._1,ltuple._2,ltuple._3,ltuple._4)
  implicit def ltuple2tuple5[T1,T2,T3,T4,T5](ltuple: LTuple5[T1,T2,T3,T4,T5]): (L[T1],L[T2],L[T3],L[T4],L[T5]) = (ltuple._1,ltuple._2,ltuple._3,ltuple._4,ltuple._5)
  implicit def ltuple2tuple6[T1,T2,T3,T4,T5,T6](ltuple: LTuple6[T1,T2,T3,T4,T5,T6]): (L[T1],L[T2],L[T3],L[T4],L[T5],L[T6]) = (ltuple._1,ltuple._2,ltuple._3,ltuple._4,ltuple._5,ltuple._6)
  implicit def ltuple2tuple7[T1,T2,T3,T4,T5,T6,T7](ltuple: LTuple7[T1,T2,T3,T4,T5,T6,T7]): (L[T1],L[T2],L[T3],L[T4],L[T5],L[T6],L[T7]) = (ltuple._1,ltuple._2,ltuple._3,ltuple._4,ltuple._5,ltuple._6,ltuple._7)
  implicit def ltuple2tuple8[T1,T2,T3,T4,T5,T6,T7,T8](ltuple: LTuple8[T1,T2,T3,T4,T5,T6,T7,T8]): (L[T1],L[T2],L[T3],L[T4],L[T5],L[T6],L[T7],L[T8]) = (ltuple._1,ltuple._2,ltuple._3,ltuple._4,ltuple._5,ltuple._6,ltuple._7,ltuple._8)
  implicit def ltuple2tuple9[T1,T2,T3,T4,T5,T6,T7,T8,T9](ltuple: LTuple9[T1,T2,T3,T4,T5,T6,T7,T8,T9]): (L[T1],L[T2],L[T3],L[T4],L[T5],L[T6],L[T7],L[T8],L[T9]) = (ltuple._1,ltuple._2,ltuple._3,ltuple._4,ltuple._5,ltuple._6,ltuple._7,ltuple._8,ltuple._9)

  def distinct[A](args: A*) : Boolean = {
    args.toList.distinct.size == args.size
  }
}
