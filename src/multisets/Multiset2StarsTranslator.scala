package multisets

object Multiset2StarsTranslator {


// start:

  def translate2QFPAfromFormulaOut(f:FormulaOut):QFPAFormula = f match {
    case FOAnd(f1,f2) => {
      val f1n = translate2QFPAfromFormulaOut(f1)
      val f2n = translate2QFPAfromFormulaOut(f2)
      QFPAAnd(f1n, f2n)
    }
    case FOOr(f1,f2) => {
      val f1n = translate2QFPAfromFormulaOut(f1)
      val f2n = translate2QFPAfromFormulaOut(f2)
      QFPAOr(f1n, f2n)
    }
    case FONot(f1)  => {
      val f1n = translate2QFPAfromFormulaOut(f1)
      QFPANot(f1n)
    }
    case FOAtom(a)  => {
      val a1 = translate2QFPAAtomfromAtomOut(a)
      QFPAAtom(a1)
    }
    case FOTrue => QFPATrue
    case FOFalse => QFPAFalse
  }


  def translate2QFPATermfromTermOut(t:TermOut):TermQFPA  = t match {
    case TOConstant(c) => TConstant(c)
    case TOVariable(v) => TVariable(v)
    case TOPlus(t1, t2) => {
      val t1n = translate2QFPATermfromTermOut(t1)
      val t2n = translate2QFPATermfromTermOut(t2)
      TPlus(t1n, t2n)
    }
    case TOTimes(c, t1)=> {
      val t1n = translate2QFPATermfromTermOut(t1)
      TTimes(c, t1n)
    }
    case TOIte(f, t1, t2)=> {
      val f1 = translate2QFPAfromFormulaOut(f)
      val t1n = translate2QFPATermfromTermOut(t1)
      val t2n = translate2QFPATermfromTermOut(t2)
      TIte(f1,t1n, t2n)
    }
    case _ => error("Impossible case ")
  }

  def translate2QFPAAtomfromAtomOut(a:AtomOut):AtomQFPA = a match {
    case AOLeq(t1,t2) => {
      val t1n = translate2QFPATermfromTermOut(t1)
      val t2n = translate2QFPATermfromTermOut(t2)
      ALeq(t1n, t2n)
    }
    case AOEq(t1,t2) => {
      val t1n = translate2QFPATermfromTermOut(t1)
      val t2n = translate2QFPATermfromTermOut(t2)
      AEq(t1n, t2n)
    }
    case _ => error("Impossible case ")
  }

  def translate2QFPAfromFormula(f:Formula):QFPAFormula = f match {
    case FAnd(f1,f2) => {
      val f1n = translate2QFPAfromFormula(f1)
      val f2n = translate2QFPAfromFormula(f2)
      QFPAAnd(f1n, f2n)
    }
    case FOr(f1,f2) => {
      val f1n = translate2QFPAfromFormula(f1)
      val f2n = translate2QFPAfromFormula(f2)
      QFPAOr(f1n, f2n)
    }
    case FNot(f1)  => {
      val f1n = translate2QFPAfromFormula(f1)
      QFPANot(f1n)
    }
    case FAtom(AAtomOut(a))  => {
      val a1 = translate2QFPAAtomfromAtomOut(a)
      QFPAAtom(a1)
    }
    case FFalse => QFPAFalse
    case FTrue => QFPATrue
    case _ => error("Impossible case ")
  }


  def translate2QFPATermfromTermIn(t:TermIn):TermQFPA  = t match {
    case TIMultiplicity(v) => TVariable(v)
    case TIConstant(c) => TConstant(c)
    case TIPlus(t1, t2) => {
      val t1n = translate2QFPATermfromTermIn(t1)
      val t2n = translate2QFPATermfromTermIn(t2)
      TPlus(t1n, t2n)
    }
    case TITimes(c, t1)=> {
      val t1n = translate2QFPATermfromTermIn(t1)
      TTimes(c, t1n)
    }
    case TIIte(f, t1, t2)=> {
      val f1 = translate2QFPAfromFormulaIn(f)
      val t1n = translate2QFPATermfromTermIn(t1)
      val t2n = translate2QFPATermfromTermIn(t2)
      TIte(f1,t1n, t2n)
    }
  }

  def translate2QFPAAtomfromAtomIn(a:AtomIn):AtomQFPA = a match {
    case AILeq(t1,t2) => {
      val t1n = translate2QFPATermfromTermIn(t1)
      val t2n = translate2QFPATermfromTermIn(t2)
      ALeq(t1n, t2n)
    }
    case AIEq(t1,t2) => {
      val t1n = translate2QFPATermfromTermIn(t1)
      val t2n = translate2QFPATermfromTermIn(t2)
      AEq(t1n, t2n)
    }
  }

  def translate2QFPAfromFormulaIn(f:FormulaIn):QFPAFormula = f match {
    case FIAnd(f1,f2) => {
      val f1n = translate2QFPAfromFormulaIn(f1)
      val f2n = translate2QFPAfromFormulaIn(f2)
      QFPAAnd(f1n, f2n)
    }
    case FIOr(f1,f2) => {
      val f1n = translate2QFPAfromFormulaIn(f1)
      val f2n = translate2QFPAfromFormulaIn(f2)
      QFPAOr(f1n, f2n)
    }
    case FINot(f1)  => {
      val f1n = translate2QFPAfromFormulaIn(f1)
      QFPANot(f1n)
    }
    case FIAtom(a)  => {
      val a1 = translate2QFPAAtomfromAtomIn(a)
      QFPAAtom(a1)
    }
    case FITrue => QFPATrue
    case FIFalse => QFPAFalse
  }

  def translate2QFPAfromForAll(f:Formula):QFPAFormula = f match {
    case FAtom(AForAllElem(f1)) => translate2QFPAfromFormulaIn(f1)
    case FFalse => QFPAFalse
    case FTrue => QFPATrue
    case _ => error("Impossible case ")
  }

  def translateListofTermsOut(v1:List[TermOut]):List[TermQFPA] = {
    var l1: List[TermQFPA] = Nil
    v1.foreach(t => {
        val tN = translate2QFPATermfromTermOut(t)
        l1 = tN :: l1
    })
    l1.reverse
  }

  def translateListofTermsIn(v1:List[TermIn]):List[TermQFPA] = {
    var l1: List[TermQFPA] = Nil
    v1.foreach(t => {
        val tN = translate2QFPATermfromTermIn(t)
        l1 = tN :: l1
    })
    l1.reverse
  }


  def getVectorValuesFromSumFormula(f:Formula):(List[TermQFPA], List[TermQFPA]) = f match {
    case FAtom(AAtomOut(AOSum(v1, FITrue, v2))) => {
      val l1 = translateListofTermsOut(v1)
      val l2 = translateListofTermsIn(v2)
      (l1, l2)
    }
    case _ => error("Impossible case ")
  }


  def nnf(f:QFPAFormula): QFPAFormula = f match {
    case QFPAAnd(f1, f2) => {
      val f1N = nnf(f1)
      val f2N = nnf(f2)
      QFPAAnd(f1N, f2N)
    }
    case QFPAOr(f1, f2) => {
      val f1N = nnf(f1)
      val f2N = nnf(f2)
      QFPAOr(f1N, f2N)
    }
    case QFPANot(QFPANot(f1)) => nnf(f1)
    case QFPANot(QFPAAnd(f1, f2)) => QFPAOr(nnf(QFPANot(f1)), nnf(QFPANot(f2)))
    case QFPANot(QFPAOr(f1, f2)) => QFPAAnd(nnf(QFPANot(f1)), nnf(QFPANot(f2)))
    case QFPANot(QFPAFalse) => QFPATrue
    case QFPANot(QFPATrue) => QFPAFalse
    case _ => f
  }



  def removeTrueAndFalse(f:QFPAFormula): QFPAFormula = f match {
    case QFPAAnd(QFPATrue, f2) => removeTrueAndFalse(f2)
    case QFPAAnd(f1, QFPATrue) => removeTrueAndFalse(f1)
    case QFPAAnd(QFPAFalse, f2) => QFPAFalse
    case QFPAAnd(f1, QFPAFalse) => QFPAFalse
    case QFPAAnd(f1, f2) => {
      val f1N = removeTrueAndFalse(f1)
      val f2N = removeTrueAndFalse(f2)
      QFPAAnd(f1N, f2N)
    }
    case QFPAOr(QFPATrue, f2) => QFPATrue
    case QFPAOr(f1, QFPATrue) => QFPATrue
    case QFPAOr(QFPAFalse, f2) => removeTrueAndFalse(f2)
    case QFPAOr(f1, QFPAFalse) => removeTrueAndFalse(f1)
    case QFPAOr(f1, f2) => {
      val f1N = removeTrueAndFalse(f1)
      val f2N = removeTrueAndFalse(f2)
      QFPAOr(f1N, f2N)
    }
    case QFPANot(f1)  => {
      val f1N = removeTrueAndFalse(f1)
      val f1NN = if (f1N == QFPATrue) QFPAFalse else 
        if (f1N == QFPAFalse) QFPATrue else QFPANot(f1N)
      f1NN
    }
    case _ => f
  }


//  start: input fPA - presburger arithmetic formula, fForAll- for all formula, fSum-sumfourmula
// output: $s1 AND $2 IN { $3 | $4} *


  def main(fPA:Formula, fForAll: Formula, fSum:Formula):(QFPAFormula, List[TermQFPA], List[TermQFPA], QFPAFormula) = {
    val f1 = removeTrueAndFalse(nnf(translate2QFPAfromFormula(fPA)))
    val f2 = removeTrueAndFalse(nnf(translate2QFPAfromForAll(fForAll)))
    val (l1, l2) = getVectorValuesFromSumFormula(fSum)
    (f1, l1, l2, f2)
  } 

}

