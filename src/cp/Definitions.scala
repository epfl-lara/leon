package cp

object Definitions {
  import Terms._
  import LTrees._

  class spec extends StaticAnnotation

  final class NotImplementedException extends Exception

  final class UnsatisfiableConstraintException extends Exception
  final class UnknownConstraintException extends Exception

  implicit def func2term0[R](func : () => R) : Term0[R] = throw new NotImplementedException
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

  implicit def forceTuple2OfL[T1,T2](tuple: (L[T1],L[T2])): (T1,T2) = tuple.value
  implicit def forceTuple3OfL[T1,T2,T3](tuple: (L[T1],L[T2],L[T3])): (T1,T2,T3) = tuple.value
  implicit def forceTuple4OfL[T1,T2,T3,T4](tuple: (L[T1],L[T2],L[T3],L[T4])): (T1,T2,T3,T4) = tuple.value
  implicit def forceTuple5OfL[T1,T2,T3,T4,T5](tuple: (L[T1],L[T2],L[T3],L[T4],L[T5])): (T1,T2,T3,T4,T5) = tuple.value
  implicit def forceTuple6OfL[T1,T2,T3,T4,T5,T6](tuple: (L[T1],L[T2],L[T3],L[T4],L[T5],L[T6])): (T1,T2,T3,T4,T5,T6) = tuple.value
  implicit def forceTuple7OfL[T1,T2,T3,T4,T5,T6,T7](tuple: (L[T1],L[T2],L[T3],L[T4],L[T5],L[T6],L[T7])): (T1,T2,T3,T4,T5,T6,T7) = tuple.value
  implicit def forceTuple8OfL[T1,T2,T3,T4,T5,T6,T7,T8](tuple: (L[T1],L[T2],L[T3],L[T4],L[T5],L[T6],L[T7],L[T8])): (T1,T2,T3,T4,T5,T6,T7,T8) = tuple.value
  implicit def forceTuple9OfL[T1,T2,T3,T4,T5,T6,T7,T8,T9](tuple: (L[T1],L[T2],L[T3],L[T4],L[T5],L[T6],L[T7],L[T8],L[T9])): (T1,T2,T3,T4,T5,T6,T7,T8,T9) = tuple.value

  implicit def tupleOfL2lTuple1[T1](lt: L[T1]): LTuple1[T1] = new LTuple1(lt)
  implicit def tupleOfL2lTuple2[T1,T2](lt: (L[T1],L[T2])): LTuple2[T1,T2] = new LTuple2(lt._1,lt._2)
  implicit def tupleOfL2lTuple3[T1,T2,T3](lt: (L[T1],L[T2],L[T3])): LTuple3[T1,T2,T3] = new LTuple3(lt._1,lt._2,lt._3)
  implicit def tupleOfL2lTuple4[T1,T2,T3,T4](lt: (L[T1],L[T2],L[T3],L[T4])): LTuple4[T1,T2,T3,T4] = new LTuple4(lt._1,lt._2,lt._3,lt._4)
  implicit def tupleOfL2lTuple5[T1,T2,T3,T4,T5](lt: (L[T1],L[T2],L[T3],L[T4],L[T5])): LTuple5[T1,T2,T3,T4,T5] = new LTuple5(lt._1,lt._2,lt._3,lt._4,lt._5)
  implicit def tupleOfL2lTuple6[T1,T2,T3,T4,T5,T6](lt: (L[T1],L[T2],L[T3],L[T4],L[T5],L[T6])): LTuple6[T1,T2,T3,T4,T5,T6] = new LTuple6(lt._1,lt._2,lt._3,lt._4,lt._5,lt._6)
  implicit def tupleOfL2lTuple7[T1,T2,T3,T4,T5,T6,T7](lt: (L[T1],L[T2],L[T3],L[T4],L[T5],L[T6],L[T7])): LTuple7[T1,T2,T3,T4,T5,T6,T7] = new LTuple7(lt._1,lt._2,lt._3,lt._4,lt._5,lt._6,lt._7)
  implicit def tupleOfL2lTuple8[T1,T2,T3,T4,T5,T6,T7,T8](lt: (L[T1],L[T2],L[T3],L[T4],L[T5],L[T6],L[T7],L[T8])): LTuple8[T1,T2,T3,T4,T5,T6,T7,T8] = new LTuple8(lt._1,lt._2,lt._3,lt._4,lt._5,lt._6,lt._7,lt._8)
  implicit def tupleOfL2lTuple9[T1,T2,T3,T4,T5,T6,T7,T8,T9](lt: (L[T1],L[T2],L[T3],L[T4],L[T5],L[T6],L[T7],L[T8],L[T9])): LTuple9[T1,T2,T3,T4,T5,T6,T7,T8,T9] = new LTuple9(lt._1,lt._2,lt._3,lt._4,lt._5,lt._6,lt._7,lt._8,lt._9)

  def distinct[A](args: A*) : Boolean = {
    args.toList.distinct.size == args.size
  }
}
