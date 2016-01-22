import leon.lazyeval._
import leon.lazyeval.Mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.lang.synthesis._

object PackratParsing0 {
  abstract class Terminal0
  
  case class Open0() extends Terminal0
  
  case class Close0() extends Terminal0
  
  case class Plus0() extends Terminal0
  
  case class Times0() extends Terminal0
  
  case class Digit0() extends Terminal0
  
  abstract class Result0
  
  case class Parsed0(rest0 : BigInt) extends Result0
  
  case class NoParse0() extends Result0
  
  def lookup3(i47 : BigInt): Terminal0 =  {
    if (i47 <= BigInt(-100)) {
      Open0()
    } else if (i47 <= BigInt(0)) {
      Close0()
    } else if (i47 <= BigInt(100)) {
      Plus0()
    } else if (i47 <= BigInt(200)) {
      Times0()
    } else {
      Digit0()
    }
  } ensuring {
    (r13 : Terminal0) => true
  }
  
  @invstate
  @memoize
  def pAdd3(i48 : BigInt, st11 : State0): (Result0, State0) =  {
    require({
      val scr2 = evalLazyResult1(newResult1(PMul0(i48), st11), st11)
      (i48 == BigInt(0) || i48 > BigInt(0) && depsEval3(i48 - BigInt(1), st11)) && st11.result0.contains(PMul0(i48)) && st11.result0.contains(PPrim0(i48)) && (scr2._1 match {
        case Parsed0(j0) =>
          ((if (j0 >= BigInt(0)) {
            depsLem3(j0, i48 - BigInt(1), scr2._2)
          } else {
            true
          }), scr2._2)
        case _ =>
          (true, scr2._2)
      })._1
    })
    val scr0 = evalLazyResult1(newResult1(PMul0(i48), st11), st11)
    scr0._1 match {
      case Parsed0(j1) =>
        if (j1 > BigInt(0) && lookup3(j1) == Plus0()) {
          val scr1 = evalLazyResult1(newResult1(PAdd0(j1 - BigInt(1)), scr0._2), scr0._2)
          scr1._1 match {
            case Parsed0(rem1) =>
              (Parsed0(rem1), scr1._2)
            case _ =>
              evalLazyResult1(newResult1(PMul0(i48), scr1._2), scr1._2)
          }
        } else {
          evalLazyResult1(newResult1(PMul0(i48), scr0._2), scr0._2)
        }
      case _ =>
        evalLazyResult1(newResult1(PMul0(i48), scr0._2), scr0._2)
    }
  } ensuring {
    (res88 : (Result0, State0)) => st11.result0 == res88._2.result0 && pAddValPred1(i48, res88._1) && (res88._1 match {
      case Parsed0(rem0) =>
        rem0 < i48
      case _ =>
        true
    })
  }
  
  def pAddUI1(i49 : BigInt): Result0 = ???[Result0]
  
  @library
  def pAddValPred1(i50 : BigInt, valres6 : Result0): Boolean =  {
    valres6 == pAddUI1(i50)
  } ensuring {
    (res82 : Boolean) => res82
  }
  
  @invstate
  @memoize
  def pMul3(i51 : BigInt, st12 : State0): (Result0, State0) =  {
    require({
      val scr7 = evalLazyResult1(newResult1(PPrim0(i51), st12), st12)
      (i51 == BigInt(0) || i51 > BigInt(0) && depsEval3(i51 - BigInt(1), st12)) && st12.result0.contains(PPrim0(i51)) && (scr7._1 match {
        case Parsed0(j2) =>
          ((if (j2 >= BigInt(0)) {
            depsLem3(j2, i51 - BigInt(1), scr7._2)
          } else {
            true
          }), scr7._2)
        case _ =>
          (true, scr7._2)
      })._1
    })
    val scr5 = evalLazyResult1(newResult1(PPrim0(i51), st12), st12)
    scr5._1 match {
      case Parsed0(j3) =>
        if (j3 > BigInt(0) && lookup3(j3) == Plus0()) {
          val scr6 = evalLazyResult1(newResult1(PMul0(j3 - BigInt(1)), scr5._2), scr5._2)
          scr6._1 match {
            case Parsed0(rem3) =>
              (Parsed0(rem3), scr6._2)
            case _ =>
              evalLazyResult1(newResult1(PPrim0(i51), scr6._2), scr6._2)
          }
        } else {
          evalLazyResult1(newResult1(PPrim0(i51), scr5._2), scr5._2)
        }
      case _ =>
        evalLazyResult1(newResult1(PPrim0(i51), scr5._2), scr5._2)
    }
  } ensuring {
    (res91 : (Result0, State0)) => st12.result0 == res91._2.result0 && pMulValPred1(i51, res91._1) && (res91._1 match {
      case Parsed0(rem2) =>
        rem2 < i51
      case _ =>
        true
    })
  }
  
  abstract class LazyResult0
  
  case class PMul0(i44 : BigInt) extends LazyResult0
  
  case class PAdd0(i45 : BigInt) extends LazyResult0
  
  case class PPrim0(i46 : BigInt) extends LazyResult0
  
  case class State0(result0 : Set[LazyResult0])
  
  def newResult1(cc1 : LazyResult0, st13 : State0): LazyResult0 = cc1
  
  @library
  def evalLazyResult1(cl2 : LazyResult0, st14 : State0): (Result0, State0) =  {
    cl2 match {
      case t140 : PMul0 =>
        val dres0 = pMul3(t140.i44, st14)
        (dres0._1, updStateResult1(dres0._2, t140))
      case t141 : PAdd0 =>
        val dres1 = pAdd3(t141.i45, st14)
        (dres1._1, updStateResult1(dres1._2, t141))
      case t142 : PPrim0 =>
        val dres2 = pPrim3(t142.i46, st14)
        (dres2._1, updStateResult1(dres2._2, t142))
    }
  } ensuring {
    (res92 : (Result0, State0)) => cl2 match {
      case t143 : PMul0 =>
        res92._1 == pMulUI1(t143.i44)
      case t144 : PAdd0 =>
        res92._1 == pAddUI1(t144.i45)
      case t145 : PPrim0 =>
        res92._1 == pPrimUI1(t145.i46)
      case _ =>
        true
    }
  }
  
  def evalLazyResultS1(cl3 : LazyResult0): Result0 = evalLazyResult1(cl3, uiResult1)._1
  
  def uiResult1(): State0 = ???[State0]
  
  def updStateResult1(st15 : State0, cl4 : LazyResult0): State0 = State0(st15.result0 ++ Set[LazyResult0](cl4))
  
  def pMulUI1(i52 : BigInt): Result0 = ???[Result0]
  
  @library
  def pMulValPred1(i53 : BigInt, valres7 : Result0): Boolean =  {
    valres7 == pMulUI1(i53)
  } ensuring {
    (res87 : Boolean) => res87
  }
  
  @invstate
  @memoize
  def pPrim3(i54 : BigInt, st16 : State0): (Result0, State0) =  {
    require(i54 == BigInt(0) || i54 > BigInt(0) && depsEval3(i54 - BigInt(1), st16))
    val char0 = lookup3(i54)
    if (char0 == Digit0()) {
      ((if (i54 > BigInt(0)) {
        Parsed0(i54 - BigInt(1))
      } else {
        Parsed0(BigInt(-1))
      }), st16)
    } else if (char0 == Open0() && i54 > BigInt(0)) {
      val scr3 = evalLazyResult1(newResult1(PAdd0(i54 - BigInt(1)), st16), st16)
      scr3._1 match {
        case Parsed0(rem5) =>
          (Parsed0(rem5), scr3._2)
        case _ =>
          (NoParse0(), scr3._2)
      }
    } else {
      (NoParse0(), st16)
    }
  } ensuring {
    (res89 : (Result0, State0)) => st16.result0 == res89._2.result0 && pPrimValPred1(i54, res89._1) && (res89._1 match {
      case Parsed0(rem4) =>
        rem4 < i54
      case _ =>
        true
    })
  }
  
  def pPrimUI1(i55 : BigInt): Result0 = ???[Result0]
  
  @library
  def pPrimValPred1(i56 : BigInt, valres8 : Result0): Boolean =  {
    valres8 == pPrimUI1(i56)
  } ensuring {
    (res83 : Boolean) => res83
  }
  
  def depsEval3(i57 : BigInt, st17 : State0): Boolean =  {
    require(i57 >= BigInt(0))
    st17.result0.contains(PPrim0(i57)) && st17.result0.contains(PMul0(i57)) && st17.result0.contains(PAdd0(i57)) && (if (i57 == BigInt(0)) {
      true
    } else {
      depsEval3(i57 - BigInt(1), st17)
    })
  } ensuring {
    (r14 : Boolean) => true
  }
  
  @traceInduct
  def evalMono3(i58 : BigInt, st11 : Set[LazyResult0], st21 : Set[LazyResult0]): Boolean =  {
    require(i58 >= BigInt(0))
    (st11.subsetOf(st21) && depsEval3(i58, State0(st11))) ==> depsEval3(i58, State0(st21))
  } ensuring {
    (holds33 : Boolean) => holds33
  }
  
  @traceInduct
  def depsLem3(x112 : BigInt, y14 : BigInt, st18 : State0): Boolean =  {
    require(x112 >= BigInt(0) && y14 >= BigInt(0))
    (x112 <= y14 && depsEval3(y14, st18)) ==> depsEval3(x112, st18)
  } ensuring {
    (holds31 : Boolean) => holds31
  }
  
  def invokeTest3(i59 : BigInt, st19 : State0): (Result0, State0) =  {
    require(i59 == BigInt(0) || i59 > BigInt(0) && depsEval3(i59 - BigInt(1), st19))
    val scr4 = evalLazyResult1(newResult1(PPrim0(i59), st19), st19)
    scr4._1 match {
      case _ =>
        evalLazyResult1(newResult1(PMul0(i59), scr4._2), scr4._2)
    }
  } ensuring {
    (r12 : (Result0, State0)) => st19.result0.subsetOf(r12._2.result0) && invokeTestValPred1(i59, r12._1)
  }
  
  def invokeTestUI1(i60 : BigInt): Result0 = ???[Result0]
  
  @library
  def invokeTestValPred1(i61 : BigInt, valres9 : Result0): Boolean =  {
    valres9 == invokeTestUI1(i61)
  } ensuring {
    (res85 : Boolean) => res85
  }
  
  def invoke3(i62 : BigInt, st20 : State0): ((Result0, Result0, Result0), State0) =  {
    require(i62 == BigInt(0) || i62 > BigInt(0) && depsEval3(i62 - BigInt(1), st20))
    val a87 = evalLazyResult1(newResult1(PPrim0(i62), st20), st20)
    val a89 = evalLazyResult1(newResult1(PMul0(i62), a87._2), a87._2)
    val a91 = evalLazyResult1(newResult1(PAdd0(i62), a89._2), a89._2)
    ((a87._1, a89._1, a91._1), a91._2)
  } ensuring {
    (res90 : ((Result0, Result0, Result0), State0)) => st20.result0.subsetOf(res90._2.result0) && invokeValPred1(i62, res90._1) && (if (i62 > BigInt(0)) {
      evalMono3(i62 - BigInt(1), st20.result0, res90._2.result0)
    } else {
      true
    }) && depsEval3(i62, res90._2)
  }
  
  def PMulpAddLem0(i48 : BigInt, st11 : State0): Boolean =  {
    {
      val scr2 = evalLazyResult1(newResult1(PMul0(i48), st11), st11)
      (i48 == BigInt(0) || i48 > BigInt(0) && depsEval3(i48 - BigInt(1), st11)) && st11.result0.contains(PMul0(i48)) && st11.result0.contains(PPrim0(i48)) && (scr2._1 match {
        case Parsed0(j0) =>
          ((if (j0 >= BigInt(0)) {
            depsLem3(j0, i48 - BigInt(1), scr2._2)
          } else {
            true
          }), scr2._2)
        case _ =>
          (true, scr2._2)
      })._1
    } ==> {
      val scr7 = evalLazyResult1(newResult1(PPrim0(i48), st11), st11)
      (i48 == BigInt(0) || i48 > BigInt(0) && depsEval3(i48 - BigInt(1), st11)) && st11.result0.contains(PPrim0(i48)) && (scr7._1 match {
        case Parsed0(j2) =>
          ((if (j2 >= BigInt(0)) {
            depsLem3(j2, i48 - BigInt(1), scr7._2)
          } else {
            true
          }), scr7._2)
        case _ =>
          (true, scr7._2)
      })._1
    }
  } ensuring {
    (holds34 : Boolean) => holds34
  }
  
  def PAddpAddLem0(i48 : BigInt, st11 : State0, scr0 : (Result0, State0), j1 : BigInt): Boolean =  {
    ({
      val scr2 = evalLazyResult1(newResult1(PMul0(i48), st11), st11)
      (i48 == BigInt(0) || i48 > BigInt(0) && depsEval3(i48 - BigInt(1), st11)) && st11.result0.contains(PMul0(i48)) && st11.result0.contains(PPrim0(i48)) && (scr2._1 match {
        case Parsed0(j0) =>
          ((if (j0 >= BigInt(0)) {
            depsLem3(j0, i48 - BigInt(1), scr2._2)
          } else {
            true
          }), scr2._2)
        case _ =>
          (true, scr2._2)
      })._1
    } && scr0 == evalLazyResult1(newResult1(PMul0(i48), st11), st11) && scr0._1.isInstanceOf[Parsed0] && j1 == scr0._1.asInstanceOf[Parsed0].rest0 && j1 > BigInt(0) && lookup3(j1) == Plus0()) ==> {
      val scr2 = evalLazyResult1(newResult1(PMul0(j1 - BigInt(1)), scr0._2), scr0._2)
      (j1 - BigInt(1) == BigInt(0) || j1 - BigInt(1) > BigInt(0) && depsEval3((j1 - BigInt(1)) - BigInt(1), scr0._2)) && scr0._2.result0.contains(PMul0(j1 - BigInt(1))) && scr0._2.result0.contains(PPrim0(j1 - BigInt(1))) && (scr2._1 match {
        case Parsed0(j0) =>
          ((if (j0 >= BigInt(0)) {
            depsLem3(j0, (j1 - BigInt(1)) - BigInt(1), scr2._2)
          } else {
            true
          }), scr2._2)
        case _ =>
          (true, scr2._2)
      })._1
    }
  } ensuring {
    (holds35 : Boolean) => holds35
  }
  
  def PMulpAddLem1(scr1 : (Result0, State0), scr0 : (Result0, State0), j1 : BigInt, i48 : BigInt, st11 : State0): Boolean =  {
    ({
      val scr2 = evalLazyResult1(newResult1(PMul0(i48), st11), st11)
      (i48 == BigInt(0) || i48 > BigInt(0) && depsEval3(i48 - BigInt(1), st11)) && st11.result0.contains(PMul0(i48)) && st11.result0.contains(PPrim0(i48)) && (scr2._1 match {
        case Parsed0(j0) =>
          ((if (j0 >= BigInt(0)) {
            depsLem3(j0, i48 - BigInt(1), scr2._2)
          } else {
            true
          }), scr2._2)
        case _ =>
          (true, scr2._2)
      })._1
    } && scr0 == evalLazyResult1(newResult1(PMul0(i48), st11), st11) && scr0._1.isInstanceOf[Parsed0] && j1 == (scr0._1.asInstanceOf[Parsed0]).rest0 && j1 > BigInt(0) && lookup3(j1) == Plus0() && scr1 == evalLazyResult1(newResult1(PAdd0(j1 - BigInt(1)), scr0._2), scr0._2) && !scr1._1.isInstanceOf[Parsed0]) ==> {
      val scr7 = evalLazyResult1(newResult1(PPrim0(i48), scr1._2), scr1._2)
      (i48 == BigInt(0) || i48 > BigInt(0) && depsEval3(i48 - BigInt(1), scr1._2)) && scr1._2.result0.contains(PPrim0(i48)) && (scr7._1 match {
        case Parsed0(j2) =>
          ((if (j2 >= BigInt(0)) {
            depsLem3(j2, i48 - BigInt(1), scr7._2)
          } else {
            true
          }), scr7._2)
        case _ =>
          (true, scr7._2)
      })._1
    }
  } ensuring {
    (holds36 : Boolean) => holds36
  }
  
  def PMulpAddLem2(i48 : BigInt, st11 : State0, scr0 : (Result0, State0), j1 : BigInt): Boolean =  {
    ({
      val scr2 = evalLazyResult1(newResult1(PMul0(i48), st11), st11)
      (i48 == BigInt(0) || i48 > BigInt(0) && depsEval3(i48 - BigInt(1), st11)) && st11.result0.contains(PMul0(i48)) && st11.result0.contains(PPrim0(i48)) && (scr2._1 match {
        case Parsed0(j0) =>
          ((if (j0 >= BigInt(0)) {
            depsLem3(j0, i48 - BigInt(1), scr2._2)
          } else {
            true
          }), scr2._2)
        case _ =>
          (true, scr2._2)
      })._1
    } && scr0 == evalLazyResult1(newResult1(PMul0(i48), st11), st11) && scr0._1.isInstanceOf[Parsed0] && j1 == (scr0._1.asInstanceOf[Parsed0]).rest0 && (j1 <= BigInt(0) || lookup3(j1) != Plus0())) ==> {
      val scr7 = evalLazyResult1(newResult1(PPrim0(i48), scr0._2), scr0._2)
      (i48 == BigInt(0) || i48 > BigInt(0) && depsEval3(i48 - BigInt(1), scr0._2)) && scr0._2.result0.contains(PPrim0(i48)) && (scr7._1 match {
        case Parsed0(j2) =>
          ((if (j2 >= BigInt(0)) {
            depsLem3(j2, i48 - BigInt(1), scr7._2)
          } else {
            true
          }), scr7._2)
        case _ =>
          (true, scr7._2)
      })._1
    }
  } ensuring {
    (holds37 : Boolean) => holds37
  }
  
  def PMulpAddLem3(i48 : BigInt, st11 : State0, scr0 : (Result0, State0)): Boolean =  {
    ({
      val scr2 = evalLazyResult1(newResult1(PMul0(i48), st11), st11)
      (i48 == BigInt(0) || i48 > BigInt(0) && depsEval3(i48 - BigInt(1), st11)) && st11.result0.contains(PMul0(i48)) && st11.result0.contains(PPrim0(i48)) && (scr2._1 match {
        case Parsed0(j0) =>
          ((if (j0 >= BigInt(0)) {
            depsLem3(j0, i48 - BigInt(1), scr2._2)
          } else {
            true
          }), scr2._2)
        case _ =>
          (true, scr2._2)
      })._1
    } && scr0 == evalLazyResult1(newResult1(PMul0(i48), st11), st11) && !scr0._1.isInstanceOf[Parsed0]) ==> {
      val scr7 = evalLazyResult1(newResult1(PPrim0(i48), scr0._2), scr0._2)
      (i48 == BigInt(0) || i48 > BigInt(0) && depsEval3(i48 - BigInt(1), scr0._2)) && scr0._2.result0.contains(PPrim0(i48)) && (scr7._1 match {
        case Parsed0(j2) =>
          ((if (j2 >= BigInt(0)) {
            depsLem3(j2, i48 - BigInt(1), scr7._2)
          } else {
            true
          }), scr7._2)
        case _ =>
          (true, scr7._2)
      })._1
    }
  } ensuring {
    (holds38 : Boolean) => holds38
  }
  
  def PPrimpMulLem0(i51 : BigInt, st12 : State0): Boolean =  {
    {
      val scr7 = evalLazyResult1(newResult1(PPrim0(i51), st12), st12)
      (i51 == BigInt(0) || i51 > BigInt(0) && depsEval3(i51 - BigInt(1), st12)) && st12.result0.contains(PPrim0(i51)) && (scr7._1 match {
        case Parsed0(j2) =>
          ((if (j2 >= BigInt(0)) {
            depsLem3(j2, i51 - BigInt(1), scr7._2)
          } else {
            true
          }), scr7._2)
        case _ =>
          (true, scr7._2)
      })._1
    } ==> (i51 == BigInt(0) || i51 > BigInt(0) && depsEval3(i51 - BigInt(1), st12))
  } ensuring {
    (holds39 : Boolean) => holds39
  }
  
  /*def PMulpMulLem0(i51 : BigInt, st12 : State0, scr5 : (Result0, State0), j3 : BigInt): Boolean =  {
    ({
      val scr7 = evalLazyResult1(newResult1(PPrim0(i51), st12), st12)
      (i51 == BigInt(0) || i51 > BigInt(0) && depsEval3(i51 - BigInt(1), st12)) && st12.result0.contains(PPrim0(i51)) && (scr7._1 match {
        case Parsed0(j2) =>
          ((if (j2 >= BigInt(0)) {
            depsLem3(j2, i51 - BigInt(1), scr7._2)
          } else {
            true
          }), scr7._2)
        case _ =>
          (true, scr7._2)
      })._1
    } && scr5 == evalLazyResult1(newResult1(PPrim0(i51), st12), st12) && scr5._1.isInstanceOf[Parsed0] && j3 == scr5._1.rest0 && j3 > BigInt(0) && lookup3(j3) == Plus0()) ==> {
      val scr7 = evalLazyResult1(newResult1(PPrim0(j3 - BigInt(1)), scr5._2), scr5._2)
      (j3 - BigInt(1) == BigInt(0) || j3 - BigInt(1) > BigInt(0) && depsEval3((j3 - BigInt(1)) - BigInt(1), scr5._2)) && scr5._2.result0.contains(PPrim0(j3 - BigInt(1))) && (scr7._1 match {
        case Parsed0(j2) =>
          ((if (j2 >= BigInt(0)) {
            depsLem3(j2, (j3 - BigInt(1)) - BigInt(1), scr7._2)
          } else {
            true
          }), scr7._2)
        case _ =>
          (true, scr7._2)
      })._1
    }
  } ensuring {
    (holds40 : Boolean) => holds40
  }
  
  def PPrimpMulLem1(i51 : BigInt, st12 : State0, scr5 : (Result0, State0), j3 : BigInt, scr6 : (Result0, State0)): Boolean =  {
    ({
      val scr7 = evalLazyResult1(newResult1(PPrim0(i51), st12), st12)
      (i51 == BigInt(0) || i51 > BigInt(0) && depsEval3(i51 - BigInt(1), st12)) && st12.result0.contains(PPrim0(i51)) && (scr7._1 match {
        case Parsed0(j2) =>
          ((if (j2 >= BigInt(0)) {
            depsLem3(j2, i51 - BigInt(1), scr7._2)
          } else {
            true
          }), scr7._2)
        case _ =>
          (true, scr7._2)
      })._1
    } && scr5 == evalLazyResult1(newResult1(PPrim0(i51), st12), st12) && scr5._1.isInstanceOf[Parsed0] && j3 == scr5._1.rest0 && j3 > BigInt(0) && lookup3(j3) == Plus0() && scr6 == evalLazyResult1(newResult1(PMul0(j3 - BigInt(1)), scr5._2), scr5._2) && !scr6._1.isInstanceOf[Parsed0]) ==> (i51 == BigInt(0) || i51 > BigInt(0) && depsEval3(i51 - BigInt(1), scr6._2))
  } ensuring {
    (holds41 : Boolean) => holds41
  }
  
  def PPrimpMulLem2(i51 : BigInt, st12 : State0, scr5 : (Result0, State0), j3 : BigInt): Boolean =  {
    ({
      val scr7 = evalLazyResult1(newResult1(PPrim0(i51), st12), st12)
      (i51 == BigInt(0) || i51 > BigInt(0) && depsEval3(i51 - BigInt(1), st12)) && st12.result0.contains(PPrim0(i51)) && (scr7._1 match {
        case Parsed0(j2) =>
          ((if (j2 >= BigInt(0)) {
            depsLem3(j2, i51 - BigInt(1), scr7._2)
          } else {
            true
          }), scr7._2)
        case _ =>
          (true, scr7._2)
      })._1
    } && scr5 == evalLazyResult1(newResult1(PPrim0(i51), st12), st12) && scr5._1.isInstanceOf[Parsed0] && j3 == scr5._1.rest0 && (j3 <= BigInt(0) || lookup3(j3) != Plus0())) ==> (i51 == BigInt(0) || i51 > BigInt(0) && depsEval3(i51 - BigInt(1), scr5._2))
  } ensuring {
    (holds42 : Boolean) => holds42
  }*/
  
  def PPrimpMulLem3(i51 : BigInt, st12 : State0, scr5 : (Result0, State0)): Boolean =  {
    ({
      val scr7 = evalLazyResult1(newResult1(PPrim0(i51), st12), st12)
      (i51 == BigInt(0) || i51 > BigInt(0) && depsEval3(i51 - BigInt(1), st12)) && st12.result0.contains(PPrim0(i51)) && (scr7._1 match {
        case Parsed0(j2) =>
          ((if (j2 >= BigInt(0)) {
            depsLem3(j2, i51 - BigInt(1), scr7._2)
          } else {
            true
          }), scr7._2)
        case _ =>
          (true, scr7._2)
      })._1
    } && scr5 == evalLazyResult1(newResult1(PPrim0(i51), st12), st12) && !scr5._1.isInstanceOf[Parsed0]) ==> (i51 == BigInt(0) || i51 > BigInt(0) && depsEval3(i51 - BigInt(1), scr5._2))
  } ensuring {
    (holds43 : Boolean) => holds43
  }
  
  def PAddpPrimLem0(i54 : BigInt, st16 : State0, char0 : Terminal0): Boolean =  {
    ((i54 == BigInt(0) || i54 > BigInt(0) && depsEval3(i54 - BigInt(1), st16)) && char0 == lookup3(i54) && char0 != Digit0() && char0 == Open0() && i54 > BigInt(0)) ==> {
      val scr2 = evalLazyResult1(newResult1(PMul0(i54 - BigInt(1)), st16), st16)
      (i54 - BigInt(1) == BigInt(0) || i54 - BigInt(1) > BigInt(0) && depsEval3((i54 - BigInt(1)) - BigInt(1), st16)) && st16.result0.contains(PMul0(i54 - BigInt(1))) && st16.result0.contains(PPrim0(i54 - BigInt(1))) && (scr2._1 match {
        case Parsed0(j0) =>
          ((if (j0 >= BigInt(0)) {
            depsLem3(j0, (i54 - BigInt(1)) - BigInt(1), scr2._2)
          } else {
            true
          }), scr2._2)
        case _ =>
          (true, scr2._2)
      })._1
    }
  } ensuring {
    (holds44 : Boolean) => holds44
  }
  
  def PPriminvokeTestLem0(i59 : BigInt, st19 : State0): Boolean =  {
    (i59 == BigInt(0) || i59 > BigInt(0) && depsEval3(i59 - BigInt(1), st19)) ==> (i59 == BigInt(0) || i59 > BigInt(0) && depsEval3(i59 - BigInt(1), st19))
  } ensuring {
    (holds45 : Boolean) => holds45
  }
  
  def PMulinvokeTestLem0(i59 : BigInt, st19 : State0, scr4 : (Result0, State0)): Boolean =  {
    ((i59 == BigInt(0) || i59 > BigInt(0) && depsEval3(i59 - BigInt(1), st19)) && scr4 == evalLazyResult1(newResult1(PPrim0(i59), st19), st19)) ==> {
      //val scr7 = evalLazyResult1(newResult1(PPrim0(i59), scr4._2), scr4._2)
      (i59 == BigInt(0) || i59 > BigInt(0) && depsEval3(i59 - BigInt(1), scr4._2)) /*&& scr4._2.result0.contains(PPrim0(i59)) && (scr7._1 match {
        case Parsed0(j2) =>
          ((if (j2 >= BigInt(0)) {
            depsLem3(j2, i59 - BigInt(1), scr7._2)
          } else {
            true
          }), scr7._2)
        case _ =>
          (true, scr7._2)
      })._1*/
    }
  } ensuring {
    (holds46 : Boolean) => holds46
  }
  
  def PPriminvokeLem0(i62 : BigInt, st20 : State0): Boolean =  {
    (i62 == BigInt(0) || i62 > BigInt(0) && depsEval3(i62 - BigInt(1), st20)) ==> (i62 == BigInt(0) || i62 > BigInt(0) && depsEval3(i62 - BigInt(1), st20))
  } ensuring {
    (holds47 : Boolean) => holds47
  }
  
  def PMulinvokeLem0(i62 : BigInt, st20 : State0, a87 : (Result0, State0)): Boolean =  {
    ((i62 == BigInt(0) || i62 > BigInt(0) && depsEval3(i62 - BigInt(1), st20)) && a87 == evalLazyResult1(newResult1(PPrim0(i62), st20), st20)) ==> {
      val scr7 = evalLazyResult1(newResult1(PPrim0(i62), a87._2), a87._2)
      (i62 == BigInt(0) || i62 > BigInt(0) && depsEval3(i62 - BigInt(1), a87._2)) && a87._2.result0.contains(PPrim0(i62)) && (scr7._1 match {
        case Parsed0(j2) =>
          ((if (j2 >= BigInt(0)) {
            depsLem3(j2, i62 - BigInt(1), scr7._2)
          } else {
            true
          }), scr7._2)
        case _ =>
          (true, scr7._2)
      })._1
    }
  } ensuring {
    (holds48 : Boolean) => holds48
  }
  
  def PAddinvokeLem0(i62 : BigInt, st20 : State0, a87 : (Result0, State0), a89 : (Result0, State0)): Boolean =  {
    ((i62 == BigInt(0) || i62 > BigInt(0) && depsEval3(i62 - BigInt(1), st20)) && a87 == evalLazyResult1(newResult1(PPrim0(i62), st20), st20) && a89 == evalLazyResult1(newResult1(PMul0(i62), a87._2), a87._2)) ==> {
      val scr2 = evalLazyResult1(newResult1(PMul0(i62), a89._2), a89._2)
      (i62 == BigInt(0) || i62 > BigInt(0) && depsEval3(i62 - BigInt(1), a89._2)) && a89._2.result0.contains(PMul0(i62)) && a89._2.result0.contains(PPrim0(i62)) && (scr2._1 match {
        case Parsed0(j0) =>
          ((if (j0 >= BigInt(0)) {
            depsLem3(j0, i62 - BigInt(1), scr2._2)
          } else {
            true
          }), scr2._2)
        case _ =>
          (true, scr2._2)
      })._1
    }
  } ensuring {
    (holds49 : Boolean) => holds49
  }
  
  def invokeUI1(i63 : BigInt): (Result0, Result0, Result0) = ???[(Result0, Result0, Result0)]
  
  @library
  def invokeValPred1(i64 : BigInt, valres10 : (Result0, Result0, Result0)): Boolean =  {
    valres10 == invokeUI1(i64)
  } ensuring {
    (res86 : Boolean) => res86
  }
  
  def bottomup3(i65 : BigInt, st21 : State0): (Result0, State0) =  {
    require(i65 >= BigInt(0))
    if (i65 == BigInt(0)) {
      val a83 = invoke3(i65, st21)
      (a83._1._3, a83._2)
    } else {
      val a82 = invoke3(i65, bottomup3(i65 - BigInt(1), st21)._2)
      (a82._1._3, a82._2)
    }
  } ensuring {
    (x$128 : (Result0, State0)) => st21.result0.subsetOf(x$128._2.result0) && bottomupValPred1(i65, x$128._1) && depsEval3(i65, x$128._2)
  }
  
  def bottomupUI1(i66 : BigInt): Result0 = ???[Result0]
  
  @library
  def bottomupValPred1(i67 : BigInt, valres11 : Result0): Boolean =  {
    valres11 == bottomupUI1(i67)
  } ensuring {
    (res84 : Boolean) => res84
  }
}
