package mapaFun

import multisets._


object MapaFunConversion {


  def createFormulaThatTwoAreDisjoint(s1: String, s2: String): Formula = {
    val a = AEqual(MIntersection(MVariable(s1), MVariable(s2)), MEmpty)
    FAtom(a)
  }

  def createFormulaThatOneIsDisjoint(s: String, l: List[String]): Formula = {
   val h = l.head
   val t = l.tail
   var ft = createFormulaThatTwoAreDisjoint(s, h)
   t.foreach(e => {
     val f1 = createFormulaThatTwoAreDisjoint(s, e)
     ft = FAnd(f1, ft)
   })
   ft
  }

  def createFormulaForDisjointness(l: List[String]): Formula = {
    var h = l.head
    var t = l.tail
    var ft = createFormulaThatOneIsDisjoint(h, t)
    while (t.length > 1) {
      h = t.head
      t = t.tail
      val f1 = createFormulaThatOneIsDisjoint(h, t)
      ft = FAnd(f1, ft)
    }
    ft
  }

  def createFormulaInItIsSet(s: String): FormulaIn = {
    val a0 = AIEq(TIMultiplicity(s), TIConstant(0))
    val a1 = AIEq(TIMultiplicity(s), TIConstant(1))
    FIOr(FIAtom(a0), FIAtom(a1))
  }

  def createFormulaInTheyAreSets(l: List[String]): FormulaIn = {
    var f1 = createFormulaInItIsSet(l.head)
    val t = l.tail
    t.foreach(s => {
      val ft = createFormulaInItIsSet(s)
      f1 = FIAnd(ft, f1)
    })
    f1
  }

  def createFormulaTheyAreSets(l: List[String]): Formula = {
    val f1 = createFormulaInTheyAreSets(l)
    FAtom(AForAllElem(f1))
  }

  def createFormulaAboutSets(l: List[String]): Formula = {
    val f1 = createFormulaTheyAreSets(l)
    if (l.length == 1) f1 else {
      val f2 = createFormulaForDisjointness(l)
      FAnd(f1, f2)
    }
  }

//-------------------

  def convertMAPAFunSet2MapaMset(s: MAPAFunSet): (Multiset, Set[String])  = s match {
    case MFSetVar(v) => (MVariable(v), Set(v))
    case MFEmptySet => (MEmpty, Set[String]())
    case MFSUnion(s1, s2) => {
      val (m1, l1) = convertMAPAFunSet2MapaMset(s1)
      val (m2, l2) = convertMAPAFunSet2MapaMset(s2)
      (MPlus(m1, m2), l1 ++ l2)
    }
    case x@_ => error("Impossible case :" + x)  
  }

  def convertMAPAFunMset2MapaMset(m: MAPAFunMultiset): (Multiset, Set[String])  = m match {
    case MFMSetVar(v) => (MVariable(v), Set[String]())
    case MFEmptyMSet => (MEmpty, Set[String]())
    case MFMUnion(m1, m2) => {
      val (m1n, l1) = convertMAPAFunMset2MapaMset(m1)
      val (m2n, l2) = convertMAPAFunMset2MapaMset(m2)
      (MUnion(m1n, m2n), l1 ++ l2)
    }
    case MFMIntersec(m1, m2) => {
      val (m1n, l1) = convertMAPAFunMset2MapaMset(m1)
      val (m2n, l2) = convertMAPAFunMset2MapaMset(m2)
      (MIntersection(m1n, m2n), l1 ++ l2)
    }
    case MFMPlus(m1, m2) => {
      val (m1n, l1) = convertMAPAFunMset2MapaMset(m1)
      val (m2n, l2) = convertMAPAFunMset2MapaMset(m2)
      (MPlus(m1n, m2n), l1 ++ l2)
    }
    case MFMMinus(m1, m2) => {
      val (m1n, l1) = convertMAPAFunMset2MapaMset(m1)
      val (m2n, l2) = convertMAPAFunMset2MapaMset(m2)
      (MMinus(m1n, m2n), l1 ++ l2)
    }
    case MFSetMinus(m1, m2) => {
      val (m1n, l1) = convertMAPAFunMset2MapaMset(m1)
      val (m2n, l2) = convertMAPAFunMset2MapaMset(m2)
      (MSetMinus(m1n, m2n), l1 ++ l2)
    }
    case MFSSetOf(m1) => {
      val (m1n, l1) = convertMAPAFunMset2MapaMset(m1)
      (MSetOf(m1n), l1)
    }
    case x@_ => error("Impossible case :" + x)  
  }


  def convertMAPAFunint2MapaTO(i: MAPAFunInt): (TermOut, Set[String])  = i match {
    case MFIntVar(v) => (TOVariable(v), Set[String]())
    case MFIntConst(c) => (TOConstant(c), Set[String]())
    case MFIPlus(i1, i2) => {
      val (t1, l1) = convertMAPAFunint2MapaTO(i1)
      val (t2, l2) = convertMAPAFunint2MapaTO(i2)
      (TOPlus(t1, t2), l1 ++ l2)
    }
    case MFITimes(c, i1) => {
      val (t1, l1) = convertMAPAFunint2MapaTO(i1)
      (TOTimes(c, t1), l1)
    }
    case MFSCard(s) => {
      val (m1, l1) = convertMAPAFunSet2MapaMset(s)
      (TOCard(m1), l1)
    }
    case MFMCard(m) => {
      val (m1, l1) = convertMAPAFunMset2MapaMset(m)
      (TOCard(m1), l1)
    }
  }

  def createFreshTO(n: Int): TermOut = {
    val s = "FRESHInt" + n
    TOVariable(s)
  }

  def convertAtomAndGetSets(a: MAPAFunAtom, i: Int): (Formula, Set[String], Int)  = a match {
    case MFSetEqual(s1, s2) => {
      val (m1, sl1) = convertMAPAFunSet2MapaMset(s1)
      val (m2, sl2) = convertMAPAFunSet2MapaMset(s2)
      (FAtom(AEqual(m1, m2)), sl1 ++ sl2, i)
    }
    case MFSetSubset(s1, s2) => {
      val (m1, sl1) = convertMAPAFunSet2MapaMset(s1)
      val (m2, sl2) = convertMAPAFunSet2MapaMset(s2)
      (FAtom(ASubset(m1, m2)), sl1 ++ sl2, i)
    }
    case MFMSetEqual(m1, m2) => {
      val (m1n, sl1) = convertMAPAFunMset2MapaMset(m1)
      val (m2n, sl2) = convertMAPAFunMset2MapaMset(m2)
      (FAtom(AEqual(m1n, m2n)), sl1 ++ sl2, i)
    }
    case MFMSetSubset(m1, m2) => {
      val (m1n, sl1) = convertMAPAFunMset2MapaMset(m1)
      val (m2n, sl2) = convertMAPAFunMset2MapaMset(m2)
      (FAtom(ASubset(m1n, m2n)), sl1 ++ sl2, i)
    }
    case MFIntEqual(i1, i2) => {
      val (i1n, sl1) = convertMAPAFunint2MapaTO(i1)
      val (i2n, sl2) = convertMAPAFunint2MapaTO(i2)
      (FAtom(AAtomOut(AOEq(i1n, i2n))), sl1 ++ sl2, i)
    }
    case MFIntLessEqual(i1, i2) => {
      val (i1n, sl1) = convertMAPAFunint2MapaTO(i1)
      val (i2n, sl2) = convertMAPAFunint2MapaTO(i2)
      (FAtom(AAtomOut(AOLeq(i1n, i2n))), sl1 ++ sl2, i)
    }
    case MFIntDivides(c, i1) => {
      val (i1n, sl1) = convertMAPAFunint2MapaTO(i1)
      val ft = createFreshTO(i)
      (FAtom(AAtomOut(AOEq(ft, TOTimes(c, i1n)))), sl1, i + 1)
    }
  }

  def convertFormulaAndGetSets(f: MAPAFunFormula, i: Int): (Formula, Set[String], Int)  = f match {
    case MFAnd(f1, f2) => {
      val (f1n, s1, i1) = convertFormulaAndGetSets(f1, i)
      val (f2n, s2, i2) = convertFormulaAndGetSets(f2, i1)
      (FAnd(f1n, f2n), s1 ++ s2, i2)
    }
    case MFOr(f1, f2) => {
      val (f1n, s1, i1) = convertFormulaAndGetSets(f1, i)
      val (f2n, s2, i2) = convertFormulaAndGetSets(f2, i1)
      (FOr(f1n, f2n), s1 ++ s2, i2)
    }
    case MFNot(f1)  => {
      val (f1n, s1, i1) = convertFormulaAndGetSets(f1, i)
      (FNot(f1n), s1, i1)
    }
    case MFAtom(a)  => convertAtomAndGetSets(a, i)
  }


//--------------------------------

  def mapaFun2standardMAPA(f: MAPAFunFormula): Formula  = {
    val (f1, s, _) = convertFormulaAndGetSets(f, 0)
// i counts fresh variables introduced for divides
    val l = s.toList
    if (l.isEmpty) f1 else {
      val f2 = createFormulaAboutSets(l)
      val ff = FAnd(f1, f2)
      ff
    }
  }


}