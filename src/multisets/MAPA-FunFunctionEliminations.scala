package mapaFun

import scala.collection.mutable.Map


object FunctionElimination {


  def createSumOfMultisets(l: List[String]): MAPAFunMultiset = {
    var mm = MFMSetVar(l.head):  MAPAFunMultiset
    val t = l.tail
    t.foreach(s => mm = MFMPlus(MFMSetVar(s), mm))
    mm
  }


  def createMultisetVariableOutofSet(s: String): String = {
    val s1 = s.replace('S', 'M')
    s1
  }


  def createListOfFreshMultisetsAndSetMultisetEqualitySet(l: List[String]): (List[String], Set[(String, String)]) = {
    var sn = Set[(String, String)]()
    var ln: List[String] = Nil
    l.foreach(e => {
      val st = createMultisetVariableOutofSet(e)
      ln = st :: ln
      sn = sn ++ Set((e, st))
    })
    (ln, sn)
  }



  def listOfSetsInUnion(s: MAPAFunSet): List[String] = s match {
    case MFSetVar(v) => List(v)
    case MFSUnion(MFSetVar(v), s1) => {
      val l1 = listOfSetsInUnion(s1)
      val l2 = v :: l1
      l2
    }
    case MFSUnion(s1, MFSetVar(v)) => {
      val l1 = listOfSetsInUnion(s1)
      val l2 = v :: l1
      l2
    }
    case MFSUnion(s1, s2) => {
      val l1 = listOfSetsInUnion(s1)
      val l2 = listOfSetsInUnion(s2)
      val l3 = l1 ::: l2
      l3
    }
    case x@_ => error("Impossible case :" + x)
  }




  def pullOutAllFunctionsFromMultiset(m: MAPAFunMultiset): (MAPAFunMultiset, Set[(String, String)])  = m match {
    case MFMSetVar(v) => (m, Set[(String, String)]())
    case MFEmptyMSet => (m, Set[(String, String)]())
    case MFMUnion(m1, m2) => {
      val (m1n, s1) = pullOutAllFunctionsFromMultiset(m1)
      val (m2n, s2) = pullOutAllFunctionsFromMultiset(m2)
      (MFMUnion(m1n, m2n), s1 ++ s2)
    }
    case MFMIntersec(m1, m2) => {
      val (m1n, s1) = pullOutAllFunctionsFromMultiset(m1)
      val (m2n, s2) = pullOutAllFunctionsFromMultiset(m2)
      (MFMIntersec(m1n, m2n), s1 ++ s2)
    }
    case MFMPlus(m1, m2) => {
      val (m1n, s1) = pullOutAllFunctionsFromMultiset(m1)
      val (m2n, s2) = pullOutAllFunctionsFromMultiset(m2)
      (MFMPlus(m1n, m2n), s1 ++ s2)
    }
    case MFMMinus(m1, m2) => {
      val (m1n, s1) = pullOutAllFunctionsFromMultiset(m1)
      val (m2n, s2) = pullOutAllFunctionsFromMultiset(m2)
      (MFMMinus(m1n, m2n), s1 ++ s2)
    }
    case MFSetMinus(m1, m2) => {
      val (m1n, s1) = pullOutAllFunctionsFromMultiset(m1)
      val (m2n, s2) = pullOutAllFunctionsFromMultiset(m2)
      (MFSetMinus(m1n, m2n), s1 ++ s2)
    }
    case MFSSetOf(m1) => {
      val (m1n, s1) = pullOutAllFunctionsFromMultiset(m1)
      (MFSSetOf(m1n), s1)
    }
    case MFFunction(f, s) => {
      val l = listOfSetsInUnion(s)
      val (ml, smes) = createListOfFreshMultisetsAndSetMultisetEqualitySet(l)
      val mf = createSumOfMultisets(ml)
      (mf, smes)
    }
  }


  def pullOutAllFunctionsFromInteger(i: MAPAFunInt): (MAPAFunInt, Set[(String, String)]) = i match {
    case MFIntVar(v) => (i, Set[(String, String)]())
    case MFIntConst(c) => (i, Set[(String, String)]())
    case MFIPlus(i1, i2) => {
      val (i1n, s1) = pullOutAllFunctionsFromInteger(i1)
      val (i2n, s2) = pullOutAllFunctionsFromInteger(i2)
      (MFIPlus(i1n, i2n), s1 ++ s2)
    }
    case MFITimes(c, i1) => {
      val (i1n, s1) = pullOutAllFunctionsFromInteger(i1)
      (MFITimes(c, i1n), s1)
    }
    case MFSCard(s) => (i, Set[(String, String)]())
    case MFMCard(m) => {
      val (m1, s1) = pullOutAllFunctionsFromMultiset(m)
      (MFMCard(m1), s1)
    }
  }


  def pullOutAllFunctionsFromAtom(a: MAPAFunAtom): (MAPAFunFormula, Set[(String, String)]) = a match {
    case MFSetEqual(s1, s2) => (MFAtom(a), Set[(String, String)]())
    case MFSetSubset(s1, s2) => (MFAtom(a), Set[(String, String)]())
    case MFMSetEqual(m1, m2) => {
      val (m1n, s1) = pullOutAllFunctionsFromMultiset(m1)
      val (m2n, s2) = pullOutAllFunctionsFromMultiset(m2)
      val an = MFMSetEqual(m1n, m2n)
      (MFAtom(an), s1 ++ s2)
    }
    case MFMSetSubset(m1, m2) => {
      val (m1n, s1) = pullOutAllFunctionsFromMultiset(m1)
      val (m2n, s2) = pullOutAllFunctionsFromMultiset(m2)
      val an = MFMSetSubset(m1n, m2n)
      (MFAtom(an), s1 ++ s2)
    }
    case MFIntEqual(i1, i2) => {
      val (i1n, s1) = pullOutAllFunctionsFromInteger(i1)
      val (i2n, s2) = pullOutAllFunctionsFromInteger(i2)
      val an = MFIntEqual(i1n, i2n)
      (MFAtom(an), s1 ++ s2)
    }
    case MFIntLessEqual(i1, i2) => {
      val (i1n, s1) = pullOutAllFunctionsFromInteger(i1)
      val (i2n, s2) = pullOutAllFunctionsFromInteger(i2)
      val an = MFIntLessEqual(i1n, i2n)
      (MFAtom(an), s1 ++ s2)
    }
    case MFIntDivides(c, i) => {
      val (in, s1) = pullOutAllFunctionsFromInteger(i)
      val an = MFIntDivides(c, in)
      (MFAtom(an), s1)
    }
  }


  def pullOutAllFunctionsFromFormula(f: MAPAFunFormula): (MAPAFunFormula, Set[(String, String)])  = f match {
    case MFAnd(f1, f2) => {
      val (f1n, s1) = pullOutAllFunctionsFromFormula(f1)
      val (f2n, s2) = pullOutAllFunctionsFromFormula(f2)
      (MFAnd(f1n, f2n), s1 ++ s2)
    }
    case MFOr(f1, f2) => {
      val (f1n, s1) = pullOutAllFunctionsFromFormula(f1)
      val (f2n, s2) = pullOutAllFunctionsFromFormula(f2)
      (MFOr(f1n, f2n), s1 ++ s2)
    }
    case MFNot(f1)  => {
      val (f1n, s1) = pullOutAllFunctionsFromFormula(f1)
      (MFNot(f1n), s1)
    }
    case MFAtom(a)  => pullOutAllFunctionsFromAtom(a)
  }



  def createOneCardinalityFormula(p: (String, String)): MAPAFunFormula = {
    val s = p._1
    val m = p._2
    val f = MFAtom(MFIntEqual(MFSCard(MFSetVar(s)), MFMCard(MFMSetVar(m))))
    f
  }


  def createCardinalityFormulas(l:  List[(String, String)]): MAPAFunFormula = {
    var ft = createOneCardinalityFormula(l.head)
    val t = l.tail
    val ff = if (t.isEmpty) ft else {
      t.foreach(p => {
        val fp = createOneCardinalityFormula(p)
        ft = MFAnd(fp, ft)
      })
      ft
    }
    ff
  }




//--------------------------------------


  def noMoreFunctions(f: MAPAFunFormula): MAPAFunFormula  = {
    val (f1, s) = pullOutAllFunctionsFromFormula(f)
    val l = s.toList
    val f2 = createCardinalityFormulas(l)
    MFAnd(f1, f2)
  }
}

