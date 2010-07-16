package multisets

import scala.collection.mutable.Set


object RemoveStars {

// start: will be needed later

  def createFormulafromConjunctions(l:List[QFPAFormula]):QFPAFormula = {
    if (l.isEmpty) QFPATrue else {
      var ff = l.head
      val fr = l.tail
      fr.foreach (f => ff = QFPAAnd(ff, f))
      ff
     }
  }


  def getAllVariablesFromTerm(t:TermQFPA): Set[String] = {
    val p = multisets.CheckingConsistency.getAllVariablesAndConstsFromTerm(t)
    p._1
  }
// end


  def updateWithNewEqualityTerm(v:String, t:TermQFPA, tt:TermQFPA):TermQFPA  = tt match {
    case TVariable(v1) => if (v == v1) t else tt
    case TConstant(c) => tt
    case TPlus(t1, t2) => {
      val t1N = updateWithNewEqualityTerm(v, t, t1)
      val t2N = updateWithNewEqualityTerm(v, t, t2)
      TPlus(t1N, t2N) 
    }
    case TTimes(c, t1) => {
      val t1N = updateWithNewEqualityTerm(v, t, t1)
      TTimes(c, t1N)
    }
    case x@_ => error("Impossible case :" + x)
  }

  def updateWithNewEqualityOneEquality(v:String, t:TermQFPA, e:QFPAFormula):QFPAFormula = e match {
    case QFPAAtom(AEq(t1, t2)) => {
      val t1N = updateWithNewEqualityTerm(v, t, t1)
      val t2N = updateWithNewEqualityTerm(v, t, t2)
      QFPAAtom(AEq(t1N, t2N)) 
    }
    case x@_ => error("Impossible case :" + x)
  }

  def updateWithNewEqualityVector(va:String, t:TermQFPA, v:List[TermQFPA]):List[TermQFPA] = 
    v.map(tt => updateWithNewEqualityTerm(va, t, tt))

  def updateWithNewEqualityEqualities(va:String, t:TermQFPA, c:List[QFPAFormula]):List[QFPAFormula] = 
    c.map(f => updateWithNewEqualityOneEquality(va, t, f))


  def isGroundTerm(t:TermQFPA):Boolean = t match {
    case TVariable(v) => false
    case TConstant(c) => true
    case TPlus(t1, t2) => {
      val b1 = isGroundTerm(t1)
      val b2 = isGroundTerm(t2)
      b1 && b2
    }
    case TTimes(c, t1) => isGroundTerm(t1)
    case TIte(f, t1, t2) => {
      val b0 = isGroundFormula(f)
      val b1 = isGroundTerm(t1)
      val b2 = isGroundTerm(t2)
      b0 && b1 && b2
    }
  }

  def isGroundAtom(a:AtomQFPA):Boolean = a match {
    case ALeq(t1, t2) => {
      val b1 = isGroundTerm(t1)
      val b2 = isGroundTerm(t2)
      b1 && b2
    }
    case AEq(t1, t2) => {
      val b1 = isGroundTerm(t1)
      val b2 = isGroundTerm(t2)
      b1 && b2
    }
  }

  def isGroundFormula(f:QFPAFormula):Boolean = f match {
    case QFPAAnd(f1, f2) => {
      val b1 = isGroundFormula(f1)
      val b2 = isGroundFormula(f2)
      b1 && b2
    }
    case QFPAOr(f1, f2) => {
      val b1 = isGroundFormula(f1)
      val b2 = isGroundFormula(f2)
      b1 && b2
    }
    case QFPANot(f1) => isGroundFormula(f1)
    case QFPAAtom(a) => isGroundAtom(a)
    case QFPAFalse => true
    case QFPATrue => true
  }


  def createTermThatIsSumOfAllTermsInList(l:List[TermQFPA]):TermQFPA = {
    val t = if (l.isEmpty) TConstant(0) else {
      var t1 = l.head
      val r = l.tail
      r.foreach(tt => t1 = TPlus(tt, t1))
      t1
    }
    t
  }


  def createTermBasedonListofValues(n:Int, l:List[(String,Int)]):TermQFPA = {
   var lt: List[TermQFPA] = Nil
   l.foreach(p => if (p._2 != 0) {
     if (p._1 == "const") {
       val m = -1 * n * p._2
       val t = TConstant(m)
       lt = t :: lt
     } else {
       val m = -1 * n * p._2
       val t = if (m == 1) TVariable(p._1) else TTimes(m, TVariable(p._1))
       lt = t :: lt
     }
   })
   val tN = createTermThatIsSumOfAllTermsInList(lt)
   tN
  }

  def createNewEqualityBasedOnListofValues(l:List[(String,Int)]):(String, TermQFPA) = {
   var notFound = true
   var lt: List[(String,Int)] = Nil
   var n = 0
   var v = ""
   l.foreach(p => if (notFound && p._1 != "const" && (p._2 == 1 || p._2 == -1)) {
     notFound = false
     v = p._1
     n = p._2
   } else lt = p :: lt)
   if (notFound) error("I am incomplete and dunno how to solve :" + lt)
   val t = createTermBasedonListofValues(n, lt)
   (v, t)
  }

  def reExpressEqualityandFindNewEquality(f:QFPAFormula):(String, TermQFPA) = f match {
    case QFPAAtom(AEq(t1, t2)) => {
      val s1 = getAllVariablesFromTerm(t1)
      val s2 = getAllVariablesFromTerm(t2)
      val s = s1 ++ s2
      val vars = s.toList
      var lt = createInitialZeroValuesList(vars)
      val l1 = addValuesofTermToList(t1, lt)
      val l2 = addValuesofTermToList(t2, lt)
      val l2N = multiplyListWithConstant(-1, l2)
      val l = sumTwoLists(l1, l2N)
      val (v, t) = createNewEqualityBasedOnListofValues(l)
      (v, t)
    }
    case x@_ => error("Impossible case :" + x)
  }


  def updateVectorVwithFormulas(v:List[TermQFPA], c:List[QFPAFormula]):List[TermQFPA] = {
   var vTemp = v
   var cTemp = c
   while (! cTemp.isEmpty) {
     val f = cTemp.head
     val cRest = cTemp.tail
     f match {
       case QFPAAtom(AEq(TVariable(va), t)) => {
         vTemp = updateWithNewEqualityVector(va, t, vTemp)
         cTemp = updateWithNewEqualityEqualities(va, t, cRest)
       }
       case QFPAAtom(AEq(t, TVariable(va))) => {
         vTemp = updateWithNewEqualityVector(va, t, vTemp)
         cTemp = updateWithNewEqualityEqualities(va, t, cRest)
       }
       case _ => {
         if (! isGroundFormula(f)) {
           val (va, t) = reExpressEqualityandFindNewEquality(f)
           vTemp = updateWithNewEqualityVector(va, t, vTemp)
           cTemp = updateWithNewEqualityEqualities(va, t, cRest)
         }
       }
     }
   }
   vTemp
  }


  def getAllVariablesFromVector(v:List[TermQFPA]):List[String] = {
    var s = Set[String]()
    v.foreach(t => {
      val s1 = getAllVariablesFromTerm(t)
      s = s ++ s1
    })
    s.toList
  }

  def createInitialZeroValuesList(v:List[String]):List[(String,Int)] = {
    var l = List(("const", 0))
    v.foreach(s => l = (s, 0) :: l)
    l.reverse
  }

  def increaseConstantCount(c:Int, l:List[(String,Int)]):List[(String,Int)] = {
    var lt: List[(String,Int)] = Nil
    l.foreach(p => if (p._1 == "const") {
      val k = p._2 + c
      lt = ("const", k) :: lt
    } else lt = p :: lt
    )
    lt.reverse
  }

  def increaseVariableCount(v:String, l:List[(String,Int)]):List[(String,Int)] = {
    var lt: List[(String,Int)] = Nil
    l.foreach(p => if (p._1 == v) {
      val c = p._2 + 1
      lt = (v, c) :: lt
    } else lt = p :: lt
    )
    lt.reverse
  }

  def sumTwoLists(l1:List[(String,Int)], l2:List[(String,Int)]):List[(String,Int)] = {
    var l: List[(String,Int)] = Nil
    val n = l1.length
    var i = 0
    while (i < n) {
      val p = l1(i)
      val n = l2(i)._2
      val s = p._2 + n
      l = (p._1, s) :: l
      i = i + 1
    }
    l.reverse
  }

  def multiplyListWithConstant(c:Int, l:List[(String,Int)]):List[(String,Int)] = {
    var lt: List[(String,Int)] = Nil
    val n = l.length
    var i = 0
    while (i < n) {
      val p = l(i)
      val s = c * p._2
      lt = (p._1, s) :: lt
      i = i + 1
    }
    lt.reverse
  }

  def addValuesofTermToList(t:TermQFPA, l:List[(String,Int)]):List[(String,Int)] = t match {
    case TVariable(v) => increaseVariableCount(v, l)
    case TConstant(c) => increaseConstantCount(c, l)
    case TPlus(t1, t2) => {
      val l1 = addValuesofTermToList(t1, l)
      val l2 = addValuesofTermToList(t2, l)
      val l3 = sumTwoLists(l1, l2)
      l3
    }
    case TTimes(c, t1) => {
      val l1 = addValuesofTermToList(t1, l)
      val l2 = multiplyListWithConstant(c, l1)
      l2
    }
    case x@_ => error("Impossible case :" + x)
  }


  def listContainingOccurancesOfVariables(t:TermQFPA, v:List[String]):List[(String,Int)] = {
    var l = createInitialZeroValuesList(v)
    val l1 = addValuesofTermToList(t, l)
    l1
  }

  def isZeroVector(v:List[Int]):Boolean = v.forall(n => (n == 0))

  def getValueinOneList(v:String, l:List[(String,Int)]):Int = {
    var n = 0
    l.foreach(p => if (p._1 == v) n = p._2)
    n
  }

  def constructIntVectorforSLS(v:String, l:List[List[(String,Int)]]):List[Int] = {
    var lt: List[Int] = Nil
    l.foreach(s => {
      val n = getValueinOneList(v, s)
      lt = n :: lt
    })
    lt
  }

  def constructLinearSetFromList(l:List[List[(String,Int)]], v:List[String]):(List[Int], List[List[Int]]) = {
    val baseVector = constructIntVectorforSLS("const", l)
    var stepVectors: List[List[Int]] = Nil
    v.foreach(s => {
      val sV = constructIntVectorforSLS(s, l)
      if (! isZeroVector(sV)) stepVectors = sV :: stepVectors
    })
    (baseVector, stepVectors)
  }


  def constructLinearSetFromThisNewVector(v:List[TermQFPA]):(List[Int], List[List[Int]]) = {
   val a1 = getAllVariablesFromVector(v)
   val n = v.length
   var i = 0
   var lB: List[List[(String,Int)]] = Nil
   while (i < n) {
     val ls = listContainingOccurancesOfVariables(v(i), a1)
     lB = ls :: lB
     i = i + 1 
   }
   val sls = constructLinearSetFromList(lB, a1)
   sls 
  }



  def createSemilinearSet(v:List[TermQFPA], c:List[QFPAFormula]):(List[Int], List[List[Int]]) = {
    val v1 = updateVectorVwithFormulas(v, c)
    val sls = constructLinearSetFromThisNewVector(v1)
    sls
  }

///////////////////

  def createTermSumFromTermList(l:List[TermQFPA]):TermQFPA = {
    val t1 = if (l.isEmpty) TConstant(0) else {
      var th = l.head
      val tt = l.tail
      tt.foreach (t => th = TPlus(th, t))
      th
    }
    t1
  }

  def createFormulaThatAllNusAreZero(s: Int, e:Int):QFPAFormula = {
    var i = s
    var lTemp: List[QFPAFormula] = Nil
    while (i < e) {
      val newNu = "FRESHnu" + i
      val eq = QFPAAtom(AEq(TVariable(newNu), TConstant(0)))
      lTemp = eq :: lTemp
      i = i + 1 
    }
    val f = createFormulafromConjunctions(lTemp)
    f
  }

  def createFormulaFromSemilinearSet(u:List[TermQFPA], slset:(List[Int], List[List[Int]]), mc:Int, nc:Int):
   (QFPAFormula, Int, Int) = {
    val n = (slset._1).length
    var i = 0
    var lTemp: List[QFPAFormula] = Nil
    val m = (slset._2).length
    val newMu = "FRESHmu" + mc
    while (i < n) {
      val t1 = if ((slset._1)(i) == 0) TConstant(0) else
        TTimes((slset._1)(i), TVariable(newMu))
      var j = 0
      var l2Temp: List[TermQFPA] = Nil 
      while (j < m) {
        val nuN = nc + j
        val newNu = "FRESHnu" + nuN
        val termTemp = if (((slset._2)(j))(i) == 0) TConstant(0) else
        TTimes(((slset._2)(j))(i), TVariable(newNu))
        l2Temp = termTemp :: l2Temp
        j = j + 1
      }
      val t2 = createTermSumFromTermList(l2Temp)
      val eq = QFPAAtom(AEq(u(i), TPlus(t1, t2)))
      lTemp = eq :: lTemp
      i = i + 1
    }
    val fNew = createFormulafromConjunctions(lTemp)
    val fMu = QFPANot(QFPAAtom(AEq(TVariable(newMu), TConstant(0))))
    val fNu = createFormulaThatAllNusAreZero(nc, nc + m)
    val constraints = QFPAOr(fMu, fNu)
    val ff = if (slset._2 == Nil) fNew else QFPAAnd(fNew, constraints)
    val mcN = mc + 1
    val ncN = nc + m
    (ff, mcN, ncN)
  }


  def createQFPAFormulaFromLIAStarFormula(u:List[TermQFPA], v:List[TermQFPA], c:List[QFPAFormula], mc: Int, nc: Int):
   (QFPAFormula, Int, Int) = {
    val slset = createSemilinearSet(v, c)
    multisets.StarFormulaPrinter.print_PAVector(v)
    print(" | ")
    c.foreach(f => {
      multisets.StarFormulaPrinter.print_QFPAFormula(f)
      print(", ")})
    println(" ")
    println("semilinear set describing it is: " + slset)
    val (fNew, m, n) = createFormulaFromSemilinearSet(u, slset, mc, nc)
    (fNew, m, n)
  }

  def removeStarsMain(f:QFPAFormula, l:List[(List[TermQFPA], List[TermQFPA], List[QFPAFormula])]):QFPAFormula = {
    var lTemp: List[QFPAFormula] = Nil
    var mc = 0
    var nc = 0
    l.foreach(t => {
      val (f1, m, n) = createQFPAFormulaFromLIAStarFormula(t._1, t._2, t._3, mc, nc)
      lTemp = f1 :: lTemp
      mc = m
      nc = n
    })
    val fTemp = createFormulafromConjunctions(lTemp)
    val g = multisets.Multiset2StarsTranslator.removeTrueAndFalse(QFPAAnd(f, fTemp))
    g
  }

}

