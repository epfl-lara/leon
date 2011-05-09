package cp

import purescala.Trees._

/** A converter has functions for converting FunCheck expressions into Scala
 * values */
class Converter(expr2scala : (Expr => Any)) {
  def exprSeq2scala1[T1](exprs : Seq[Expr]) : (T1) =
    (expr2scala(exprs(0)).asInstanceOf[T1])

  def exprSeq2scala2[T1,T2](exprs : Seq[Expr]) : (T1,T2) =
    (expr2scala(exprs(0)).asInstanceOf[T1],expr2scala(exprs(1)).asInstanceOf[T2])

  def exprSeq2scala3[T1,T2,T3](exprs : Seq[Expr]) : (T1,T2,T3) =
    (expr2scala(exprs(0)).asInstanceOf[T1],expr2scala(exprs(1)).asInstanceOf[T2],expr2scala(exprs(2)).asInstanceOf[T3])

  def exprSeq2scala4[T1,T2,T3,T4](exprs : Seq[Expr]) : (T1,T2,T3,T4) =
    (expr2scala(exprs(0)).asInstanceOf[T1],expr2scala(exprs(1)).asInstanceOf[T2],expr2scala(exprs(2)).asInstanceOf[T3],expr2scala(exprs(3)).asInstanceOf[T4])

  def exprSeq2scala5[T1,T2,T3,T4,T5](exprs : Seq[Expr]) : (T1,T2,T3,T4,T5) =
    (expr2scala(exprs(0)).asInstanceOf[T1],expr2scala(exprs(1)).asInstanceOf[T2],expr2scala(exprs(2)).asInstanceOf[T3],expr2scala(exprs(3)).asInstanceOf[T4],expr2scala(exprs(4)).asInstanceOf[T5])

  def exprSeq2scala6[T1,T2,T3,T4,T5,T6](exprs : Seq[Expr]) : (T1,T2,T3,T4,T5,T6) =
    (expr2scala(exprs(0)).asInstanceOf[T1],expr2scala(exprs(1)).asInstanceOf[T2],expr2scala(exprs(2)).asInstanceOf[T3],expr2scala(exprs(3)).asInstanceOf[T4],expr2scala(exprs(4)).asInstanceOf[T5],expr2scala(exprs(5)).asInstanceOf[T6])

  def exprSeq2scala7[T1,T2,T3,T4,T5,T6,T7](exprs : Seq[Expr]) : (T1,T2,T3,T4,T5,T6,T7) =
    (expr2scala(exprs(0)).asInstanceOf[T1],expr2scala(exprs(1)).asInstanceOf[T2],expr2scala(exprs(2)).asInstanceOf[T3],expr2scala(exprs(3)).asInstanceOf[T4],expr2scala(exprs(4)).asInstanceOf[T5],expr2scala(exprs(5)).asInstanceOf[T6],expr2scala(exprs(6)).asInstanceOf[T7])

  def exprSeq2scala8[T1,T2,T3,T4,T5,T6,T7,T8](exprs : Seq[Expr]) : (T1,T2,T3,T4,T5,T6,T7,T8) =
    (expr2scala(exprs(0)).asInstanceOf[T1],expr2scala(exprs(1)).asInstanceOf[T2],expr2scala(exprs(2)).asInstanceOf[T3],expr2scala(exprs(3)).asInstanceOf[T4],expr2scala(exprs(4)).asInstanceOf[T5],expr2scala(exprs(5)).asInstanceOf[T6],expr2scala(exprs(6)).asInstanceOf[T7],expr2scala(exprs(7)).asInstanceOf[T8])

  def exprSeq2scala9[T1,T2,T3,T4,T5,T6,T7,T8,T9](exprs : Seq[Expr]) : (T1,T2,T3,T4,T5,T6,T7,T8,T9) =
    (expr2scala(exprs(0)).asInstanceOf[T1],expr2scala(exprs(1)).asInstanceOf[T2],expr2scala(exprs(2)).asInstanceOf[T3],expr2scala(exprs(3)).asInstanceOf[T4],expr2scala(exprs(4)).asInstanceOf[T5],expr2scala(exprs(5)).asInstanceOf[T6],expr2scala(exprs(6)).asInstanceOf[T7],expr2scala(exprs(7)).asInstanceOf[T8],expr2scala(exprs(8)).asInstanceOf[T9])

}
