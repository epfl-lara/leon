import leon.lazyeval._
import leon.lazyeval.Mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.lang.synthesis._

object PackratParsing {
  abstract class Terminal
  
  case class Open() extends Terminal
  
  case class Close() extends Terminal
  
  case class Plus() extends Terminal
  
  case class Times() extends Terminal
  
  case class Digit() extends Terminal
  
  abstract class Result
  
  case class Parsed(rest : BigInt) extends Result
  
  case class NoParse() extends Result
  
  def lookup(i : BigInt): Terminal =  {
    if (i <= BigInt(-100)) {
      Open()
    } else if (i <= BigInt(0)) {
      Close()
    } else if (i <= BigInt(100)) {
      Plus()
    } else if (i <= BigInt(200)) {
      Times()
    } else {
      Digit()
    }
  } ensuring {
    (r : Terminal) => true
  }
  
  
  
  def pAdd(i : BigInt, st : State): (Result, State) =  {
    require({
      val scr = evalLazyResult(newResult(PMul(i), st), st)
      (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st)) && st.result.contains(PMul(i)) && st.result.contains(PPrim(i)) && (scr._1 match {
        case Parsed(j) =>
          ((if (j >= BigInt(0)) {
            depsLem(j, i - BigInt(1), scr._2)
          } else {
            true
          }), scr._2)
        case _ =>
          (true, scr._2)
      })._1
    })
    val scr = evalLazyResult(newResult(PMul(i), st), st)
    scr._1 match {
      case Parsed(j) =>
        if (j > BigInt(0) && lookup(j) == Plus()) {
          val scr = evalLazyResult(newResult(PAdd(j - BigInt(1)), scr._2), scr._2)
          scr._1 match {
            case Parsed(rem) =>
              (Parsed(rem), scr._2)
            case _ =>
              evalLazyResult(newResult(PMul(i), scr._2), scr._2)
          }
        } else {
          evalLazyResult(newResult(PMul(i), scr._2), scr._2)
        }
      case _ =>
        evalLazyResult(newResult(PMul(i), scr._2), scr._2)
    }
  } ensuring {
    (res : (Result, State)) => st.result == res._2.result && pAddValPred(i, res._1) && (res._1 match {
      case Parsed(rem) =>
        rem < i
      case _ =>
        true
    })
  }
  
  def pAddUI(i : BigInt): Result = ???[Result]
  
  @library
  def pAddValPred(i : BigInt, valres : Result): Boolean =  {
    valres == pAddUI(i)
  } ensuring {
    (res : Boolean) => res
  }
  
  
  
  def pMul(i : BigInt, st : State): (Result, State) =  {
    require({
      val scr = evalLazyResult(newResult(PPrim(i), st), st)
      (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st)) && st.result.contains(PPrim(i)) && (scr._1 match {
        case Parsed(j) =>
          ((if (j >= BigInt(0)) {
            depsLem(j, i - BigInt(1), scr._2)
          } else {
            true
          }), scr._2)
        case _ =>
          (true, scr._2)
      })._1
    })
    val scr = evalLazyResult(newResult(PPrim(i), st), st)
    scr._1 match {
      case Parsed(j) =>
        if (j > BigInt(0) && lookup(j) == Plus()) {
          val scr = evalLazyResult(newResult(PMul(j - BigInt(1)), scr._2), scr._2)
          scr._1 match {
            case Parsed(rem) =>
              (Parsed(rem), scr._2)
            case _ =>
              evalLazyResult(newResult(PPrim(i), scr._2), scr._2)
          }
        } else {
          evalLazyResult(newResult(PPrim(i), scr._2), scr._2)
        }
      case _ =>
        evalLazyResult(newResult(PPrim(i), scr._2), scr._2)
    }
  } ensuring {
    (res : (Result, State)) => st.result == res._2.result && pMulValPred(i, res._1) && (res._1 match {
      case Parsed(rem) =>
        rem < i
      case _ =>
        true
    })
  }
  
  abstract class LazyResult
  
  case class PMul(i : BigInt) extends LazyResult
  
  case class PAdd(i : BigInt) extends LazyResult
  
  case class PPrim(i : BigInt) extends LazyResult
  
  case class State(result : Set[LazyResult])
  
  def newResult(cc : LazyResult, st : State): LazyResult = cc
  
  @library
  def evalLazyResult(cl : LazyResult, st : State): (Result, State) =  {
    cl match {
      case t : PMul =>
        val dres = pMul(t.i, st)
        (dres._1, updStateResult(dres._2, t))
      case t : PAdd =>
        val dres = pAdd(t.i, st)
        (dres._1, updStateResult(dres._2, t))
      case t : PPrim =>
        val dres = pPrim(t.i, st)
        (dres._1, updStateResult(dres._2, t))
    }
  } ensuring {
    (res : (Result, State)) => cl match {
      case t : PMul =>
        res._1 == pMulUI(t.i)
      case t : PAdd =>
        res._1 == pAddUI(t.i)
      case t : PPrim =>
        res._1 == pPrimUI(t.i)
      case _ =>
        true
    }
  }
  
  def evalLazyResultS(cl : LazyResult): Result = evalLazyResult(cl, uiResult)._1
  
  def uiResult(): State = ???[State]
  
  def updStateResult(st : State, cl : LazyResult): State = State(st.result ++ Set[LazyResult](cl))
  
  def pMulUI(i : BigInt): Result = ???[Result]
  
  @library
  def pMulValPred(i : BigInt, valres : Result): Boolean =  {
    valres == pMulUI(i)
  } ensuring {
    (res : Boolean) => res
  }
    
  def pPrim(i : BigInt, st : State): (Result, State) =  {
    require(i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st))
    val char = lookup(i)
    if (char == Digit()) {
      ((if (i > BigInt(0)) {
        Parsed(i - BigInt(1))
      } else {
        Parsed(BigInt(-1))
      }), st)
    } else if (char == Open() && i > BigInt(0)) {
      val scr = evalLazyResult(newResult(PAdd(i - BigInt(1)), st), st)
      scr._1 match {
        case Parsed(rem) =>
          (Parsed(rem), scr._2)
        case _ =>
          (NoParse(), scr._2)
      }
    } else {
      (NoParse(), st)
    }
  } ensuring {
    (res : (Result, State)) => st.result == res._2.result && pPrimValPred(i, res._1) && (res._1 match {
      case Parsed(rem) =>
        rem < i
      case _ =>
        true
    })
  }
  
  def pPrimUI(i : BigInt): Result = ???[Result]
  
  @library
  def pPrimValPred(i : BigInt, valres : Result): Boolean =  {
    valres == pPrimUI(i)
  } ensuring {
    (res : Boolean) => res
  }
  
  def depsEval(i : BigInt, st : State): Boolean =  {
    require(i >= BigInt(0))
    st.result.contains(PPrim(i)) && st.result.contains(PMul(i)) && st.result.contains(PAdd(i)) && (if (i == BigInt(0)) {
      true
    } else {
      depsEval(i - BigInt(1), st)
    })
  } ensuring {
    (r : Boolean) => true
  }
  
  @traceInduct
  def evalMono(i : BigInt, st1 : Set[LazyResult], st2 : Set[LazyResult]): Boolean =  {
    require(i >= BigInt(0))
    (st1.subsetOf(st2) && depsEval(i, State(st1))) ==> depsEval(i, State(st2))
  } ensuring {
    (holds33 : Boolean) => holds33
  }
  
  @traceInduct
  def depsLem(x : BigInt, y : BigInt, st : State): Boolean =  {
    require(x >= BigInt(0) && y >= BigInt(0))
    (x <= y && depsEval(y, st)) ==> depsEval(x, st)
  } ensuring {
    (holds : Boolean) => holds
  }
  
  def invokeTest(i : BigInt, st : State): (Result, State) =  {
    require(i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st))
    val scr = evalLazyResult(newResult(PPrim(i), st), st)
    scr._1 match {
      case _ =>
        evalLazyResult(newResult(PMul(i), scr._2), scr._2)
    }
  } ensuring {
    (r : (Result, State)) => st.result.subsetOf(r._2.result) && invokeTestValPred(i, r._1)
  }
  
  def invokeTestUI(i : BigInt): Result = ???[Result]

  
  @library
  def invokeTestValPred(i : BigInt, valres : Result): Boolean =  {
    valres == invokeTestUI(i)
  } ensuring {
    (res : Boolean) => res
  }
  
  def invoke(i : BigInt, st : State): ((Result, Result, Result), State) =  {
    require(i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st))
    val a87 = evalLazyResult(newResult(PPrim(i), st), st)
    val a89 = evalLazyResult(newResult(PMul(i), a87._2), a87._2)
    val a91 = evalLazyResult(newResult(PAdd(i), a89._2), a89._2)
    ((a87._1, a89._1, a91._1), a91._2)
  } ensuring {
    (res : ((Result, Result, Result), State)) => st.result.subsetOf(res._2.result) && invokeValPred(i, res._1) && (if (i > BigInt(0)) {
      evalMono(i - BigInt(1), st.result, res._2.result)
    } else {
      true
    }) && depsEval(i, res._2)
  }
  
  def PMulpAddLem(i : BigInt, st : State): Boolean =  {
    {
      val scr = evalLazyResult(newResult(PMul(i), st), st)
      (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st)) && st.result.contains(PMul(i)) && st.result.contains(PPrim(i)) && (scr._1 match {
        case Parsed(j) =>
          ((if (j >= BigInt(0)) {
            depsLem(j, i - BigInt(1), scr._2)
          } else {
            true
          }), scr._2)
        case _ =>
          (true, scr._2)
      })._1
    } ==> {
      val scr = evalLazyResult(newResult(PPrim(i), st), st)
      (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st)) && st.result.contains(PPrim(i)) && (scr._1 match {
        case Parsed(j) =>
          ((if (j >= BigInt(0)) {
            depsLem(j, i - BigInt(1), scr._2)
          } else {
            true
          }), scr._2)
        case _ =>
          (true, scr._2)
      })._1
    }
  } ensuring {
    (holds : Boolean) => holds
  }
  
  def PAddpAddLem(i : BigInt, st : State, scr : (Result, State), j : BigInt): Boolean =  {
    ({
      val scr = evalLazyResult(newResult(PMul(i), st), st)
      (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st)) && st.result.contains(PMul(i)) && st.result.contains(PPrim(i)) && (scr._1 match {
        case Parsed(j) =>
          ((if (j >= BigInt(0)) {
            depsLem(j, i - BigInt(1), scr._2)
          } else {
            true
          }), scr._2)
        case _ =>
          (true, scr._2)
      })._1
    } && scr == evalLazyResult(newResult(PMul(i), st), st) && scr._1.isInstanceOf[Parsed] && j == scr._1.rest && j > BigInt(0) && lookup(j) == Plus()) ==> {
      val scr = evalLazyResult(newResult(PMul(j - BigInt(1)), scr._2), scr._2)
      (j - BigInt(1) == BigInt(0) || j - BigInt(1) > BigInt(0) && depsEval((j - BigInt(1)) - BigInt(1), scr._2)) && scr._2.result.contains(PMul(j - BigInt(1))) && scr._2.result.contains(PPrim(j - BigInt(1))) && (scr._1 match {
        case Parsed(j) =>
          ((if (j >= BigInt(0)) {
            depsLem(j, (j - BigInt(1)) - BigInt(1), scr._2)
          } else {
            true
          }), scr._2)
        case _ =>
          (true, scr._2)
      })._1
    }
  } ensuring {
    (holds : Boolean) => holds
  }
  
  def PMulpAddLem1(scr : (Result, State), scr : (Result, State), j : BigInt, i : BigInt, st : State): Boolean =  {
    ({
      val scr = evalLazyResult(newResult(PMul(i), st), st)
      (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st)) && st.result.contains(PMul(i)) && st.result.contains(PPrim(i)) && (scr._1 match {
        case Parsed(j) =>
          ((if (j >= BigInt(0)) {
            depsLem(j, i - BigInt(1), scr._2)
          } else {
            true
          }), scr._2)
        case _ =>
          (true, scr._2)
      })._1
    } && scr == evalLazyResult(newResult(PMul(i), st), st) && scr._1.isInstanceOf[Parsed] && j == scr._1.rest && j > BigInt(0) && lookup(j) == Plus() && scr == evalLazyResult(newResult(PAdd(j - BigInt(1)), scr._2), scr._2) && !scr._1.isInstanceOf[Parsed]) ==> {
      val scr = evalLazyResult(newResult(PPrim(i), scr._2), scr._2)
      (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), scr._2)) && scr._2.result.contains(PPrim(i)) && (scr._1 match {
        case Parsed(j) =>
          ((if (j >= BigInt(0)) {
            depsLem(j, i - BigInt(1), scr._2)
          } else {
            true
          }), scr._2)
        case _ =>
          (true, scr._2)
      })._1
    }
  } ensuring {
    (holds : Boolean) => holds
  }
  
  def PMulpAddLem2(i : BigInt, st : State, scr : (Result, State), j : BigInt): Boolean =  {
    ({
      val scr = evalLazyResult(newResult(PMul(i), st), st)
      (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st)) && st.result.contains(PMul(i)) && st.result.contains(PPrim(i)) && (scr._1 match {
        case Parsed(j) =>
          ((if (j >= BigInt(0)) {
            depsLem(j, i - BigInt(1), scr._2)
          } else {
            true
          }), scr._2)
        case _ =>
          (true, scr._2)
      })._1
    } && scr == evalLazyResult(newResult(PMul(i), st), st) && scr._1.isInstanceOf[Parsed] && j == scr._1.rest && (j <= BigInt(0) || lookup(j) != Plus())) ==> {
      val scr = evalLazyResult(newResult(PPrim(i), scr._2), scr._2)
      (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), scr._2)) && scr._2.result.contains(PPrim(i)) && (scr._1 match {
        case Parsed(j) =>
          ((if (j >= BigInt(0)) {
            depsLem(j, i - BigInt(1), scr._2)
          } else {
            true
          }), scr._2)
        case _ =>
          (true, scr._2)
      })._1
    }
  } ensuring {
    (holds : Boolean) => holds
  }
  
  def PMulpAddLem3(i : BigInt, st : State, scr : (Result, State)): Boolean =  {
    ({
      val scr = evalLazyResult(newResult(PMul(i), st), st)
      (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st)) && st.result.contains(PMul(i)) && st.result.contains(PPrim(i)) && (scr._1 match {
        case Parsed(j) =>
          ((if (j >= BigInt(0)) {
            depsLem(j, i - BigInt(1), scr._2)
          } else {
            true
          }), scr._2)
        case _ =>
          (true, scr._2)
      })._1
    } && scr == evalLazyResult(newResult(PMul(i), st), st) && !scr._1.isInstanceOf[Parsed]) ==> {
      val scr = evalLazyResult(newResult(PPrim(i), scr._2), scr._2)
      (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), scr._2)) && scr._2.result.contains(PPrim(i)) && (scr._1 match {
        case Parsed(j) =>
          ((if (j >= BigInt(0)) {
            depsLem(j, i - BigInt(1), scr._2)
          } else {
            true
          }), scr._2)
        case _ =>
          (true, scr._2)
      })._1
    }
  } ensuring {
    (holds : Boolean) => holds
  }
  
  def PPrimpMulLem(i : BigInt, st : State): Boolean =  {
    {
      val scr = evalLazyResult(newResult(PPrim(i), st), st)
      (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st)) && st.result.contains(PPrim(i)) && (scr._1 match {
        case Parsed(j) =>
          ((if (j >= BigInt(0)) {
            depsLem(j, i - BigInt(1), scr._2)
          } else {
            true
          }), scr._2)
        case _ =>
          (true, scr._2)
      })._1
    } ==> (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st))
  } ensuring {
    (holds : Boolean) => holds
  }
  
  def PMulpMulLem(i : BigInt, st : State, scr : (Result, State), j : BigInt): Boolean =  {
    ({
      val scr = evalLazyResult(newResult(PPrim(i), st), st)
      (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st)) && st.result.contains(PPrim(i)) && (scr._1 match {
        case Parsed(j) =>
          ((if (j >= BigInt(0)) {
            depsLem(j, i - BigInt(1), scr._2)
          } else {
            true
          }), scr._2)
        case _ =>
          (true, scr._2)
      })._1
    } && scr == evalLazyResult(newResult(PPrim(i), st), st) && scr._1.isInstanceOf[Parsed] && j == scr._1.rest && j > BigInt(0) && lookup(j) == Plus()) ==> {
      val scr = evalLazyResult(newResult(PPrim(j - BigInt(1)), scr._2), scr._2)
      (j - BigInt(1) == BigInt(0) || j - BigInt(1) > BigInt(0) && depsEval((j - BigInt(1)) - BigInt(1), scr._2)) && scr._2.result.contains(PPrim(j - BigInt(1))) && (scr._1 match {
        case Parsed(j) =>
          ((if (j >= BigInt(0)) {
            depsLem(j, (j - BigInt(1)) - BigInt(1), scr._2)
          } else {
            true
          }), scr._2)
        case _ =>
          (true, scr._2)
      })._1
    }
  } ensuring {
    (holds : Boolean) => holds
  }
  
  def PPrimpMulLem1(i : BigInt, st : State, scr : (Result, State), j : BigInt, scr : (Result, State)): Boolean =  {
    ({
      val scr = evalLazyResult(newResult(PPrim(i), st), st)
      (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st)) && st.result.contains(PPrim(i)) && (scr._1 match {
        case Parsed(j) =>
          ((if (j >= BigInt(0)) {
            depsLem(j, i - BigInt(1), scr._2)
          } else {
            true
          }), scr._2)
        case _ =>
          (true, scr._2)
      })._1
    } && scr == evalLazyResult(newResult(PPrim(i), st), st) && scr._1.isInstanceOf[Parsed] && j == scr._1.rest && j > BigInt(0) && lookup(j) == Plus() && scr == evalLazyResult(newResult(PMul(j - BigInt(1)), scr._2), scr._2) && !scr._1.isInstanceOf[Parsed]) ==> (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), scr._2))
  } ensuring {
    (holds : Boolean) => holds
  }
  
  def PPrimpMulLem2(i : BigInt, st : State, scr : (Result, State), j : BigInt): Boolean =  {
    ({
      val scr = evalLazyResult(newResult(PPrim(i), st), st)
      (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st)) && st.result.contains(PPrim(i)) && (scr._1 match {
        case Parsed(j) =>
          ((if (j >= BigInt(0)) {
            depsLem(j, i - BigInt(1), scr._2)
          } else {
            true
          }), scr._2)
        case _ =>
          (true, scr._2)
      })._1
    } && scr == evalLazyResult(newResult(PPrim(i), st), st) && scr._1.isInstanceOf[Parsed] && j == scr._1.rest && (j <= BigInt(0) || lookup(j) != Plus())) ==> (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), scr._2))
  } ensuring {
    (holds : Boolean) => holds
  }
  
  def PPrimpMulLem3(i : BigInt, st : State, scr : (Result, State)): Boolean =  {
    ({
      val scr = evalLazyResult(newResult(PPrim(i), st), st)
      (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st)) && st.result.contains(PPrim(i)) && (scr._1 match {
        case Parsed(j) =>
          ((if (j >= BigInt(0)) {
            depsLem(j, i - BigInt(1), scr._2)
          } else {
            true
          }), scr._2)
        case _ =>
          (true, scr._2)
      })._1
    } && scr == evalLazyResult(newResult(PPrim(i), st), st) && !scr._1.isInstanceOf[Parsed]) ==> (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), scr._2))
  } ensuring {
    (holds : Boolean) => holds
  }
  
  def PAddpPrimLem(i : BigInt, st : State, char : Terminal): Boolean =  {
    ((i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st)) && char == lookup(i) && char != Digit() && char == Open() && i > BigInt(0)) ==> {
      val scr = evalLazyResult(newResult(PMul(i - BigInt(1)), st), st)
      (i - BigInt(1) == BigInt(0) || i - BigInt(1) > BigInt(0) && depsEval((i - BigInt(1)) - BigInt(1), st)) && st.result.contains(PMul(i - BigInt(1))) && st.result.contains(PPrim(i - BigInt(1))) && (scr._1 match {
        case Parsed(j) =>
          ((if (j >= BigInt(0)) {
            depsLem(j, (i - BigInt(1)) - BigInt(1), scr._2)
          } else {
            true
          }), scr._2)
        case _ =>
          (true, scr._2)
      })._1
    }
  } ensuring {
    (holds : Boolean) => holds
  }
  
  def PPriminvokeTestLem(i : BigInt, st : State): Boolean =  {
    (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st)) ==> (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st))
  } ensuring {
    (holds : Boolean) => holds
  }
  
  def PMulinvokeTestLem(i : BigInt, st : State, scr : (Result, State)): Boolean =  {
    ((i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st)) && scr == evalLazyResult(newResult(PPrim(i), st), st)) ==> {
      val scr = evalLazyResult(newResult(PPrim(i), scr._2), scr._2)
      (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), scr._2)) && scr._2.result.contains(PPrim(i)) && (scr._1 match {
        case Parsed(j) =>
          ((if (j >= BigInt(0)) {
            depsLem(j, i - BigInt(1), scr._2)
          } else {
            true
          }), scr._2)
        case _ =>
          (true, scr._2)
      })._1
    }
  } ensuring {
    (holds : Boolean) => holds
  }
  
  def PPriminvokeLem(i : BigInt, st : State): Boolean =  {
    (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st)) ==> (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st))
  } ensuring {
    (holds : Boolean) => holds
  }
  
  def PMulinvokeLem(i : BigInt, st : State, a87 : (Result, State)): Boolean =  {
    ((i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st)) && a87 == evalLazyResult(newResult(PPrim(i), st), st)) ==> {
      val scr = evalLazyResult(newResult(PPrim(i), a87._2), a87._2)
      (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), a87._2)) && a87._2.result.contains(PPrim(i)) && (scr._1 match {
        case Parsed(j) =>
          ((if (j >= BigInt(0)) {
            depsLem(j, i - BigInt(1), scr._2)
          } else {
            true
          }), scr._2)
        case _ =>
          (true, scr._2)
      })._1
    }
  } ensuring {
    (holds : Boolean) => holds
  }
  
  def PAddinvokeLem(i : BigInt, st : State, a87 : (Result, State), a89 : (Result, State)): Boolean =  {
    ((i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), st)) && a87 == evalLazyResult(newResult(PPrim(i), st), st) && a89 == evalLazyResult(newResult(PMul(i), a87._2), a87._2)) ==> {
      val scr = evalLazyResult(newResult(PMul(i), a89._2), a89._2)
      (i == BigInt(0) || i > BigInt(0) && depsEval(i - BigInt(1), a89._2)) && a89._2.result.contains(PMul(i)) && a89._2.result.contains(PPrim(i)) && (scr._1 match {
        case Parsed(j) =>
          ((if (j >= BigInt(0)) {
            depsLem(j, i - BigInt(1), scr._2)
          } else {
            true
          }), scr._2)
        case _ =>
          (true, scr._2)
      })._1
    }
  } ensuring {
    (holds : Boolean) => holds
  }
  
  def invokeUI(i : BigInt): (Result, Result, Result) = ???[(Result, Result, Result)]
  
  @library
  def invokeValPred(i : BigInt, valres : (Result, Result, Result)): Boolean =  {
    valres == invokeUI(i)
  } ensuring {
    (res : Boolean) => res
  }
  
  def bottomup(i : BigInt, st : State): (Result, State) =  {
    require(i >= BigInt(0))
    if (i == BigInt(0)) {
      val a83 = invoke(i, st)
      (a83._1._3, a83._2)
    } else {
      val a82 = invoke(i, bottomup(i - BigInt(1), st)._2)
      (a82._1._3, a82._2)
    }
  } ensuring {
    (x$1 : (Result, State)) => st.result.subsetOf(xst._2.result) && bottomupValPred(i, x$1._1) && depsEval(i, x$1._2)
  }
  
  def bottomupUI(i : BigInt): Result = ???[Result]
  
  @library
  def bottomupValPred(i : BigInt, valres : Result): Boolean =  {
    valres == bottomupUI(i)
  } ensuring {
    (res : Boolean) => res
  }
}
