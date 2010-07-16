package mapaFun


import scala.collection.mutable.Map
import scala.collection.immutable.Set
import java.lang.Integer



object SetExpansionAndCNF {








// ---- getRidOfSetVariables


  def simplifySetAtoms(s1: Set[String], s2: Set[String]): (Set[String], Set[String]) = {
    val si = s1.intersect(s2)
    val s1n = s1 -- si
    val s2n = s2 -- si
    (s1n, s2n)
  }


  def getRidOfSetVariablesinSet(s: MAPAFunSet, m: Map[String,Set[String]]): Set[String] = s match {
    case MFSetVar(v) => m(v)
    case MFEmptySet => Set[String]()
    case MFUnivSet => m("ALL")
    case MFSUnion(s1, s2) => {
      val ss1 = getRidOfSetVariablesinSet(s1, m)
      val ss2 = getRidOfSetVariablesinSet(s2, m)
      ss1 ++ ss2
    }
    case MFSIntersec(s1, s2) => {
      val ss1 = getRidOfSetVariablesinSet(s1, m)
      val ss2 = getRidOfSetVariablesinSet(s2, m)
      val ss3 = ss1.intersect(ss2)
      ss3
    }
    case MFSCompl(s1) => {
      val ss1 = getRidOfSetVariablesinSet(s1, m)
      val ss2 = m("ALL") -- ss1
      ss2
    }
  }

  def createSetUnion(s: Set[String]): MAPAFunSet =  {
    val l = s.toList
    if (l.isEmpty) MFEmptySet else {
       var ts =  MFSetVar(l.head): MAPAFunSet
       val t = l.tail
       t.foreach(e => {
         val ns = MFSetVar(e)
         ts = MFSUnion(ts, ns)
       })
       ts
    }
  }

  def getRidOfSetVariablesinInt(i: MAPAFunInt, m: Map[String,Set[String]]): MAPAFunInt  = i match {
    case MFIntVar(v) => i
    case MFIntConst(c) => i
    case MFIPlus(i1, i2) => {
      val i1n = getRidOfSetVariablesinInt(i1, m)
      val i2n = getRidOfSetVariablesinInt(i2, m)
      MFIPlus(i1n, i2n)
    }
    case MFITimes(c, i1) => {
      val i1n = getRidOfSetVariablesinInt(i1, m)
      MFITimes(c, i1n)
    }
    case MFSCard(s) => {
      val sl = getRidOfSetVariablesinSet(s, m)
      val sn = createSetUnion(sl)
      MFSCard(sn)
    }
    case MFMCard(ms) => {
      val msn = getRidOfSetVariablesinMultiset(ms, m)
      MFMCard(msn)
    }
  }

  def getRidOfSetVariablesinMultiset(mm: MAPAFunMultiset, m: Map[String,Set[String]]): MAPAFunMultiset  = mm match {
    case MFMSetVar(v) => mm
    case MFEmptyMSet => mm
    case MFMUnion(m1, m2) => {
      val m1n = getRidOfSetVariablesinMultiset(m1, m)
      val m2n = getRidOfSetVariablesinMultiset(m2, m)
      MFMUnion(m1n, m2n)
    }
    case MFMIntersec(m1, m2) => {
      val m1n = getRidOfSetVariablesinMultiset(m1, m)
      val m2n = getRidOfSetVariablesinMultiset(m2, m)
      MFMIntersec(m1n, m2n)
    }
    case MFMPlus(m1, m2) => {
      val m1n = getRidOfSetVariablesinMultiset(m1, m)
      val m2n = getRidOfSetVariablesinMultiset(m2, m)
      MFMPlus(m1n, m2n)
    }
    case MFMMinus(m1, m2) => {
      val m1n = getRidOfSetVariablesinMultiset(m1, m)
      val m2n = getRidOfSetVariablesinMultiset(m2, m)
      MFMMinus(m1n, m2n)
    }
    case MFSetMinus(m1, m2) => {
      val m1n = getRidOfSetVariablesinMultiset(m1, m)
      val m2n = getRidOfSetVariablesinMultiset(m2, m)
      MFSetMinus(m1n, m2n)
    }
    case MFSSetOf(m1) => {
      val m1n = getRidOfSetVariablesinMultiset(m1, m)
      MFSSetOf(m1n)
    }
    case MFFunction(f, s) => {
      val sl = getRidOfSetVariablesinSet(s, m)
      val sn = createSetUnion(sl)
      MFFunction(f, sn)
    }
  }


  def getRidOfSetVariablesinAtom(a:MAPAFunAtom, m: Map[String,Set[String]]): MAPAFunAtom  = a match {
    case MFSetEqual(s1, s2) => {
      val ss1l = getRidOfSetVariablesinSet(s1, m)
      val ss2l = getRidOfSetVariablesinSet(s2, m)
      val (ss1ln, ss2ln) = simplifySetAtoms(ss1l, ss2l)
      val s1n = createSetUnion(ss1ln)
      val s2n = createSetUnion(ss2ln)
      MFSetEqual(s1n, s2n)
    }
    case MFSetSubset(s1, s2) => {
      val ss1l = getRidOfSetVariablesinSet(s1, m)
      val ss2l = getRidOfSetVariablesinSet(s2, m)
      val (ss1ln, ss2ln) = simplifySetAtoms(ss1l, ss2l)
      val s1n = createSetUnion(ss1ln)
      val s2n = createSetUnion(ss2ln)
      MFSetSubset(s1n, s2n)
    }
    case MFMSetEqual(m1, m2) => {
      val m1n = getRidOfSetVariablesinMultiset(m1, m)
      val m2n = getRidOfSetVariablesinMultiset(m2, m)
      MFMSetEqual(m1n, m2n)
    }
    case MFMSetSubset(m1, m2) => {
      val m1n = getRidOfSetVariablesinMultiset(m1, m)
      val m2n = getRidOfSetVariablesinMultiset(m2, m)
      MFMSetSubset(m1n, m2n)
    }
    case MFIntEqual(i1, i2) => {
      val i1n = getRidOfSetVariablesinInt(i1, m)
      val i2n = getRidOfSetVariablesinInt(i2, m)
      MFIntEqual(i1n, i2n)
    }
    case MFIntLessEqual(i1, i2) => {
      val i1n = getRidOfSetVariablesinInt(i1, m)
      val i2n = getRidOfSetVariablesinInt(i2, m)
      MFIntLessEqual(i1n, i2n)
    }
    case MFIntDivides(c, i) => {
      val in = getRidOfSetVariablesinInt(i, m)
      MFIntDivides(c, in)
    }
  }


  def getRidOfSetVariables(f: MAPAFunFormula, m: Map[String,Set[String]]): MAPAFunFormula = f match {
    case MFAnd(f1, f2) => {
      val f1n = getRidOfSetVariables(f1, m)
      val f2n = getRidOfSetVariables(f2, m)
      MFAnd(f1n, f2n)
    }
    case MFOr(f1, f2) => {
      val f1n = getRidOfSetVariables(f1, m)
      val f2n = getRidOfSetVariables(f2, m)
      MFOr(f1n, f2n)
    }
    case MFNot(f1) => {
      val f1n = getRidOfSetVariables(f1, m)
      MFNot(f1n)
    }
    case MFAtom(a) =>{
      val an = getRidOfSetVariablesinAtom(a, m)
      MFAtom(an)
    } 
  }







// ---- list of all sets 

  def setofAllSetsinInt(i: MAPAFunInt): Set[String] = i match {
    case MFIntVar(v) => Set[String]()
    case MFIntConst(c) => Set[String]()
    case MFIPlus(i1, i2) => {
      val l1 = setofAllSetsinInt(i1)
      val l2 = setofAllSetsinInt(i2)
      l1 ++ l2
    }
    case MFITimes(c, i1) => setofAllSetsinInt(i1)
    case MFSCard(s) => setofAllSetsinSet(s)
    case MFMCard(m) => setofAllSetsinMultiset(m)
  }

  def setofAllSetsinMultiset(m: MAPAFunMultiset): Set[String] = m match {
    case MFMSetVar(v) => Set[String]()
    case MFEmptyMSet => Set[String]()
    case MFMUnion(m1, m2) => {
      val l1 = setofAllSetsinMultiset(m1)
      val l2 = setofAllSetsinMultiset(m2)
      l1 ++ l2
    }
    case MFMIntersec(m1, m2) => {
      val l1 = setofAllSetsinMultiset(m1)
      val l2 = setofAllSetsinMultiset(m2)
      l1 ++ l2
    }
    case MFMPlus(m1, m2) => {
      val l1 = setofAllSetsinMultiset(m1)
      val l2 = setofAllSetsinMultiset(m2)
      l1 ++ l2
    }
    case MFMMinus(m1, m2) => {
      val l1 = setofAllSetsinMultiset(m1)
      val l2 = setofAllSetsinMultiset(m2)
      l1 ++ l2
    }
    case MFSetMinus(m1, m2) => {
      val l1 = setofAllSetsinMultiset(m1)
      val l2 = setofAllSetsinMultiset(m2)
      l1 ++ l2
    }
    case MFSSetOf(m1) => setofAllSetsinMultiset(m1)
    case MFFunction(f, s) => setofAllSetsinSet(s)
  }

  def setofAllSetsinSet(s: MAPAFunSet): Set[String]  = s match {
    case MFSetVar(v) => Set(v)
    case MFEmptySet => Set[String]()
    case MFUnivSet => Set[String]()
    case MFSUnion(s1, s2) => {
      val l1 = setofAllSetsinSet(s1)
      val l2 = setofAllSetsinSet(s2)
      l1 ++ l2
    }
    case MFSIntersec(s1, s2) => {
      val l1 = setofAllSetsinSet(s1)
      val l2 = setofAllSetsinSet(s2)
      l1 ++ l2
    }
    case MFSCompl(s1) => setofAllSetsinSet(s1)
  }

  def setofAllSetsinAtom(a: MAPAFunAtom): Set[String] = a match {
    case MFSetEqual(s1, s2) => {
      val l1 = setofAllSetsinSet(s1)
      val l2 = setofAllSetsinSet(s2)
      l1 ++ l2
    }
    case MFSetSubset(s1, s2) => {
      val l1 = setofAllSetsinSet(s1)
      val l2 = setofAllSetsinSet(s2)
      l1 ++ l2
    }
    case MFMSetEqual(m1, m2) => {
      val l1 = setofAllSetsinMultiset(m1)
      val l2 = setofAllSetsinMultiset(m2)
      l1 ++ l2
    }
    case MFMSetSubset(m1, m2) => {
      val l1 = setofAllSetsinMultiset(m1)
      val l2 = setofAllSetsinMultiset(m2)
      l1 ++ l2
    }
    case MFIntEqual(i1, i2) => {
      val l1 = setofAllSetsinInt(i1)
      val l2 = setofAllSetsinInt(i2)
      l1 ++ l2
    }
    case MFIntLessEqual(i1, i2) => {
      val l1 = setofAllSetsinInt(i1)
      val l2 = setofAllSetsinInt(i2)
      l1 ++ l2
    }
    case MFIntDivides(c, i) => setofAllSetsinInt(i)
  }

  def setofAllSets(f: MAPAFunFormula): Set[String] = f match {
    case MFAnd(f1, f2) => {
      val s1 = setofAllSets(f1)
      val s2 = setofAllSets(f2)
      s1 ++ s2
    }
    case MFOr(f1, f2) => {
      val s1 = setofAllSets(f1)
      val s2 = setofAllSets(f2)
      s1 ++ s2
    }
    case MFNot(f1)  => setofAllSets(f1)
    case MFAtom(a)  => setofAllSetsinAtom(a)
  }

  def power2(n: Int): Int = {
    var i = 1
    for(k <- 1 to n) i = i * 2
    i
  }

  def createListOfExponentialSize(n: Int): List[List[String]] = {
    if (n == 0) Nil
    else {
      val ub = power2 (n - 1)
      var l1: List[List[String]] = Nil
      for (i <- 0 to (ub - 1) ) {
        val s = (Integer.toBinaryString(i)).toList
        var s1 = s.map (_.toString)
        while (s1.length < (n - 1)) {
          s1 = "0" :: s1
        }
        l1 = s1 :: l1
      }
      l1
    }
  }

  def createStringfromList(i: Int, l: List[String]): String = {
    val ln = l.take(i) ::: ( "1" :: l.drop(i) )
    ln.mkString("S", "", "")
  }


  def createCubesForSet(i: Int, l: List[List[String]]): Set[String] = {
    var s = Set[String]()
    l.foreach(l1 => {
      val st = createStringfromList(i, l1)
      s = s ++ Set(st)
    })
    s
  }


  def createUniversalSetCubes(l: List[List[String]]): Set[String] = {
    var s = Set[String]()
    l.foreach(e => {
      val l0 = "0" :: e
      val s0 = l0.mkString("S", "", "")
      s = s ++ Set(s0)
      val l1 = "1" :: e
      val s1 = l1.mkString("S", "", "")
      s = s ++ Set(s1)
    })
    s
  }

  def createMapOfNewCubes(l: List[String]): Map[String,Set[String]] = {
    val tm = Map[String, Set[String]]()
    val n = l.length
    var i = 0
    val ls = createListOfExponentialSize(n)
    l.foreach(e => {
      val nl = createCubesForSet(i, ls)
      i = i + 1
      tm += (e -> nl)
      }
    )
    val us = createUniversalSetCubes(ls)
    tm += ("ALL" -> us)
    tm
  }

  def listOfAllSets(f: MAPAFunFormula): Map[String,Set[String]] = {
    val s1 = setofAllSets(f)
    val l1 = s1.toList
    val m1 = createMapOfNewCubes(l1)
    m1
  }


//--------------------------------------

  def noMoreSets(f: MAPAFunFormula): MAPAFunFormula = {
    val l1 = listOfAllSets(f)
    val f1 = getRidOfSetVariables(f, l1)
    f1
  }

}

