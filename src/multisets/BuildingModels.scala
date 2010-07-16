package multisets


import scala.collection.mutable.Map
import java.lang.Integer



object reconstructingModels {

  def addNewValuestoMap(l:List[String], i: Int, m: Map[String, Int]): Map[String, Int] = {
    var mt = m
    l.foreach(s => mt += (s -> i))
    mt
  }

  def getIntValueFromString(s: String): Int = {
   val s1 = s.replaceAll(":int", "")
   val n = Integer.parseInt(s1)
   n
  }

  def getAllVariablesFromString(s: String): List[String] = {
    val i1 = s.indexOf('{') 
    val i2 = s.indexOf('}')
    val s1 = s.substring(i1 + 1, i2)
    val vars = s1.split(" ")
    val l1 = vars.toList 
    l1
  }


  def extractModelAndAddtoMap(s: String, m: Map[String, Int]): Map[String, Int] = {
    if (s.startsWith("*"))  {
      val strings = s.split (" -> ");
      val l = getAllVariablesFromString(strings(0))
      val n = getIntValueFromString(strings(1))
      val m1 = addNewValuestoMap(l, n, m)
      m1
    } else m
  }

  def createSatisfyingAssignmentforQFPA(ls: List[String]): Map[String, Int] = {
    var tm = Map[String, Int]()
    ls.foreach(s => {
       tm = extractModelAndAddtoMap(s, tm)
    })
    tm
  }

// ======================


  def replaceVectorsStartingWithSomeStringWithValuesinTerm(t: TermQFPA, m: Map[String, Int], s: String): TermQFPA = t match {
    case TConstant(c) => t
    case TVariable(v) => {
      if (v.contains(s)) {
        val nv = m(v)
        TConstant(nv)
      } else t
    }
    case TPlus(t1, t2) => {
      val t1n = replaceVectorsStartingWithSomeStringWithValuesinTerm(t1, m, s)
      val t2n = replaceVectorsStartingWithSomeStringWithValuesinTerm(t2, m, s)
      TPlus(t1n, t2n)
    }
    case TTimes(c, t1) => {
      val t1n = replaceVectorsStartingWithSomeStringWithValuesinTerm(t1, m, s)
      TTimes(c, t1n)
    }
    case TIte(f, t1, t2) => {
      val fn = replaceVectorsStartingWithSomeStringWithValues(f, m, s)
      val t1n = replaceVectorsStartingWithSomeStringWithValuesinTerm(t1, m, s)
      val t2n = replaceVectorsStartingWithSomeStringWithValuesinTerm(t2, m, s)
      TIte(fn, t1n, t2n)
    }
  }


  def replaceVectorsStartingWithSomeStringWithValuesinAtom(a: AtomQFPA, m: Map[String, Int], s: String): AtomQFPA = a match {
    case ALeq(t1,t2) => {
      val t1n = replaceVectorsStartingWithSomeStringWithValuesinTerm(t1, m, s)
      val t2n = replaceVectorsStartingWithSomeStringWithValuesinTerm(t2, m, s)
      ALeq(t1n, t2n)
    }
    case AEq(t1,t2) => {
      val t1n = replaceVectorsStartingWithSomeStringWithValuesinTerm(t1, m, s)
      val t2n = replaceVectorsStartingWithSomeStringWithValuesinTerm(t2, m, s)
      AEq(t1n, t2n)
    }
  }

  def replaceVectorsStartingWithSomeStringWithValues(f: QFPAFormula, m: Map[String, Int], s: String): QFPAFormula = f match {
    case QFPAAnd(f1,f2) => {
      val f1n = replaceVectorsStartingWithSomeStringWithValues(f1, m, s)
      val f2n = replaceVectorsStartingWithSomeStringWithValues(f2, m, s)
      QFPAAnd(f1n, f2n)
    }
    case QFPAOr(f1,f2) => {
      val f1n = replaceVectorsStartingWithSomeStringWithValues(f1, m, s)
      val f2n = replaceVectorsStartingWithSomeStringWithValues(f2, m, s)
      QFPAOr(f1n, f2n)
    }
    case QFPANot(f1)  => {
      val f1n = replaceVectorsStartingWithSomeStringWithValues(f1, m, s)
      QFPANot(f1n)
    }
    case QFPAAtom(a)  => {
      val a1 = replaceVectorsStartingWithSomeStringWithValuesinAtom(a, m, s)
      QFPAAtom(a1)
    }
    case QFPAFalse => f
    case QFPATrue  => f
  }

  def isNumericalTerm(t: TermQFPA): (Boolean, Int) = t match {
    case TConstant(c) => (true, c)
    case TVariable(v) => (false, 0)
    case TPlus(t1, t2) => {
      val (b1, c1) = isNumericalTerm(t1)
      val (b2, c2) = isNumericalTerm(t2)
      (b1 && b2, c1 + c2)
    }
    case TTimes(c, t1) => {
      val (b1, c1) = isNumericalTerm(t1)
      (b1, c * c1)
    }
    case TIte(f, t1, t2) => {
      val f1 = evaluatePureNumericalExpressions(f)
      val (b1, c1) = isNumericalTerm(t1)
      val (b2, c2) = isNumericalTerm(t2)
      val f2 = evaluatePureBooleanExpressions(f1)
      if (f2 == QFPATrue) (b1, c1) else 
        if (f2 == QFPANot(QFPATrue)) (b2, c2) else
          (false, 0)
    }
  }

  def evaluatePureNumericalExpressioninTerm(t: TermQFPA): TermQFPA = t match {
    case TConstant(c) => t
    case TVariable(v) => t
    case TPlus(t1, t2) => {
      val t1n = evaluatePureNumericalExpressioninTerm(t1)
      val t2n = evaluatePureNumericalExpressioninTerm(t2)
      val (b1, c1) = isNumericalTerm(t1n)
      val (b2, c2) = isNumericalTerm(t2n)
      if (b1 && b2) {
        val c = c1 + c2
        TConstant(c)
      } else { if (b1 && c1 == 0) t2n
          else if (b2 && c2 == 0) t1n else TPlus(t1n, t2n)
      }
    }
    case TTimes(c, t1) => {
      val t1n = evaluatePureNumericalExpressioninTerm(t1)
      val (b1, c1) = isNumericalTerm(t1n)
      if (b1) {
        val cf = c * c1
        TConstant(cf)
      } else TTimes(c, t1n)
    }
    case TIte(f, t1, t2) => {
      val f1 = evaluatePureNumericalExpressions(f)
      val t1n = evaluatePureNumericalExpressioninTerm(t1)
      val t2n = evaluatePureNumericalExpressioninTerm(t2)
      val f2 = evaluatePureBooleanExpressions(f1)
      if (f2 == QFPATrue) t1n else 
        if (f2 == QFPANot(QFPATrue)) t2n else
          TIte(f2, t1n, t2n)
    }
  }

  def evaluatePureNumericalExpressioninAtom(a: AtomQFPA): AtomQFPA = a match {
    case ALeq(t1,t2) => {
      val t1n = evaluatePureNumericalExpressioninTerm(t1)
      val t2n = evaluatePureNumericalExpressioninTerm(t2)
      ALeq(t1n, t2n)
    }
    case AEq(t1,t2) => {
      val t1n = evaluatePureNumericalExpressioninTerm(t1)
      val t2n = evaluatePureNumericalExpressioninTerm(t2)
      AEq(t1n, t2n)
    }
  }

  def evaluatePureNumericalExpressions(f: QFPAFormula): QFPAFormula = f match {
    case QFPAAnd(f1,f2) => {
      val f1n = evaluatePureNumericalExpressions(f1)
      val f2n = evaluatePureNumericalExpressions(f2)
      QFPAAnd(f1n, f2n)
    }
    case QFPAOr(f1,f2) => {
      val f1n = evaluatePureNumericalExpressions(f1)
      val f2n = evaluatePureNumericalExpressions(f2)
      QFPAOr(f1n, f2n)
    }
    case QFPANot(f1)  => {
      val f1n = evaluatePureNumericalExpressions(f1)
      QFPANot(f1n)
    }
    case QFPAAtom(a)  => {
      val a1 = evaluatePureNumericalExpressioninAtom(a)
      QFPAAtom(a1)
    }
    case QFPAFalse => f
    case QFPATrue  => f
  }



  def evaluatePureBooleanExpressionsinAtom(a: AtomQFPA): QFPAFormula = a match {
    case ALeq(t1, t2) => {
      if (t1 == t2) QFPATrue else {
        val (b1, c1) = isNumericalTerm(t1)
        val (b2, c2) = isNumericalTerm(t2)
        if (b1 && b2) {
          if (c1 <= c2) QFPATrue else QFPANot(QFPATrue)
        } else QFPAAtom(a)
      }
    }
    case AEq(t1,t2) => {
      if (t1 == t2) QFPATrue else {
        val (b1, c1) = isNumericalTerm(t1)
        val (b2, c2) = isNumericalTerm(t2)
        if (b1 && b2) {
          if (c1 == c2) QFPATrue else QFPANot(QFPATrue)
        } else QFPAAtom(a)
      }
    }
  }


  def evaluatePureBooleanExpressions(f: QFPAFormula): QFPAFormula = f match {
    case QFPAAnd(f1,f2) => {
      val f1n = evaluatePureBooleanExpressions(f1)
      val f2n = evaluatePureBooleanExpressions(f2)
      if (f1n == QFPANot(QFPATrue) || f2n == QFPANot(QFPATrue)) QFPANot(QFPATrue) else
        if (f1n == QFPATrue) f2n else
          if (f2n == QFPATrue) f1n else
            QFPAAnd(f1n, f2n)
    }
    case QFPAOr(f1,f2) => {
      val f1n = evaluatePureBooleanExpressions(f1)
      val f2n = evaluatePureBooleanExpressions(f2)
      if (f1n == QFPATrue || f2n == QFPATrue) QFPATrue else
        if (f1n == QFPANot(QFPATrue)) f2n else
          if (f2n == QFPANot(QFPATrue)) f1n else
            QFPAOr(f1n, f2n)
    }
    case QFPANot(f1)  => {
      val f1n = evaluatePureBooleanExpressions(f1)
      val f2n = f1n match {
        case QFPANot(f3n) => f3n
        case _ => QFPANot(f1n)
      }
      f2n
    }
    case QFPAAtom(a)  => evaluatePureBooleanExpressionsinAtom(a)
    case QFPAFalse => f
    case QFPATrue  => f
  }


  def simplifyArithmeticExpressionsInQFPA(f: QFPAFormula): QFPAFormula = {
    val f1 = evaluatePureNumericalExpressions(f)
    val f2 = evaluatePureBooleanExpressions(f1)
    f2
 }


  def evaluateFormulaForVariablesStartingWith(f: QFPAFormula, m: Map[String, Int], s: String): QFPAFormula = {
    val f1 = replaceVectorsStartingWithSomeStringWithValues(f, m, s)
    val f2 = simplifyArithmeticExpressionsInQFPA(f1)
    f2
  }


// ===========================

  def deriveValueofVarTermInModel(t: TermQFPA, m: Map[String, Int]): Int  = t match {
    case TConstant(c) => c
    case TVariable(v) => m(v)
    case x@_ => error("Impossible case :" + x)
  }

  def isNulVectorinGivenModel(t: List[TermQFPA], m: Map[String, Int]): Boolean = {
    val t1 = t.map(tm => deriveValueofVarTermInModel(tm, m))
    t1.forall(tm => (tm == 0))
  }



  def replaceAllTermsWithZeroinTerm(t: TermQFPA, l: List[TermQFPA]): TermQFPA = t match {
    case TConstant(c) => t
    case TVariable(v) => if (l.contains(t)) TConstant(0) else t
    case TPlus(t1, t2) => {
      val t1n = replaceAllTermsWithZeroinTerm(t1, l)
      val t2n = replaceAllTermsWithZeroinTerm(t2, l)
      TPlus(t1n, t2n)
    }
    case TTimes(c, t1) => {
      val t1n = replaceAllTermsWithZeroinTerm(t1, l)
      TTimes(c, t1n)
    }
    case TIte(f, t1, t2) => {
      val fn = replaceAllTermsWithZero(f, l)
      val t1n = replaceAllTermsWithZeroinTerm(t1, l)
      val t2n = replaceAllTermsWithZeroinTerm(t2, l)
      TIte(fn, t1n, t2n)
    }
  }

  def replaceAllTermsWithZeroinAtom(a: AtomQFPA, t: List[TermQFPA]): AtomQFPA = a match {
    case ALeq(t1,t2) => {
      val t1n =  replaceAllTermsWithZeroinTerm(t1, t)
      val t2n =  replaceAllTermsWithZeroinTerm(t2, t)
      ALeq(t1n, t2n)
    }
    case AEq(t1,t2) => {
      val t1n =  replaceAllTermsWithZeroinTerm(t1, t)
      val t2n =  replaceAllTermsWithZeroinTerm(t2, t)
      AEq(t1n, t2n)
    }
  }

  def replaceAllTermsWithZero(f: QFPAFormula, t: List[TermQFPA]): QFPAFormula = f match {
    case QFPAAnd(f1,f2) => {
      val f1n = replaceAllTermsWithZero(f1, t)
      val f2n = replaceAllTermsWithZero(f2, t)
      QFPAAnd(f1n, f2n)
    }
    case QFPAOr(f1,f2) => {
      val f1n = replaceAllTermsWithZero(f1, t)
      val f2n = replaceAllTermsWithZero(f2, t)
      QFPAOr(f1n, f2n)
    }
    case QFPANot(f1)  => {
      val f1n = replaceAllTermsWithZero(f1, t)
      QFPANot(f1n)
    }
    case QFPAAtom(a)  => {
      val a1 = replaceAllTermsWithZeroinAtom(a, t)
      QFPAAtom(a1)
    }
    case QFPAFalse => f
    case QFPATrue  => f
  }

  def removeZeroVectorInFormula(f: QFPAFormula, t: List[TermQFPA]): QFPAFormula = {
    val f1 = replaceAllTermsWithZero(f, t)
    val f2 = simplifyArithmeticExpressionsInQFPA(f1) 
    f2
  }
}

