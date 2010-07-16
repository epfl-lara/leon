package multisets


import scala.collection.mutable.Set


object CreateDisjunctions {

// start: input formula
// output: formula without ITE Expresssions and formula denoting ITE experssions

  def flattenITEExpressionsTerm(t:TermQFPA, vc:Int, il:List[(String,TermQFPA)]):(TermQFPA,Int,List[(String,TermQFPA)]) = t match {
     case TPlus(t1, t2) => {
      val (t1N, vc1, il1) = flattenITEExpressionsTerm(t1, vc, il)
      val (t2N, vc2, il2) = flattenITEExpressionsTerm(t2, vc1, il1)
      (TPlus(t1N, t2N), vc2, il2)
    }
     case TTimes(c, t1) => {
      val (t1N, vc1, il1) = flattenITEExpressionsTerm(t1, vc, il)
      (TTimes(c, t1N), vc1, il1)
     }
     case TIte(f, t1, t2) => {
       val newITEVar = "FRESHv" + vc
       var il1 = (newITEVar, t)  :: il
       (TVariable(newITEVar), vc + 1, il1)
     }
     case _ => (t, vc, il)
  }

  def flattenITEExpressionsAtom(a:AtomQFPA, vc:Int, il:List[(String,TermQFPA)]):(QFPAFormula,Int,List[(String,TermQFPA)]) = a match {
     case ALeq(t1, t2) => {
      val (t1N, vc1, il1) = flattenITEExpressionsTerm(t1, vc, il)
      val (t2N, vc2, il2) = flattenITEExpressionsTerm(t2, vc1, il1)
      (QFPAAtom(ALeq(t1N, t2N)), vc2, il2)
    }
     case AEq(t1, t2) => {
      val (t1N, vc1, il1) = flattenITEExpressionsTerm(t1, vc, il)
      val (t2N, vc2, il2) = flattenITEExpressionsTerm(t2, vc1, il1)
      (QFPAAtom(AEq(t1N, t2N)), vc2, il2)
    }
  }

  def flattenITEExpressionsFormula(f:QFPAFormula, vc:Int, il:List[(String,TermQFPA)]):(QFPAFormula,Int,List[(String,TermQFPA)]) = f match {
    case QFPAAnd(f1, f2) => {
      val (f1N, vc1, il1) = flattenITEExpressionsFormula(f1, vc, il)
      val (f2N, vc2, il2) = flattenITEExpressionsFormula(f2, vc1, il1)
      (QFPAAnd(f1N, f2N), vc2, il2)
    }
    case QFPAOr(f1, f2) => {
      val (f1N, vc1, il1) = flattenITEExpressionsFormula(f1, vc, il)
      val (f2N, vc2, il2) = flattenITEExpressionsFormula(f2, vc1, il1)
      (QFPAOr(f1N, f2N), vc2, il2)
    }
    case QFPANot(f1) => {
      val (f1N, vc1, il1) = flattenITEExpressionsFormula(f1, vc, il)
      (QFPANot(f1N), vc1, il1)
    }
    case QFPAAtom(a) => flattenITEExpressionsAtom(a, vc, il)
    case _ => (f, vc, il)
  }

 def flatten_ITEList(il:List[(String,TermQFPA)],ic:Int, toBeFlattened: Boolean):List[(String,TermQFPA)] = {
    var addedFreshITEs = false
    var ilN:List[(String,TermQFPA)] = Nil
    var icN = ic
    if (toBeFlattened) {
      il.foreach(p => p._2 match {
        case TIte(f, t1, t2) => {
          var iltmp:List[(String,TermQFPA)] = Nil
          val (fF, ic1, il1) = flattenITEExpressionsFormula(f, icN, iltmp)
          val (t1F, ic2, il2) = flattenITEExpressionsTerm(t1, ic1, il1)
          val (t2F, ic3, il3) = flattenITEExpressionsTerm(t2, ic2, il2)
          if (il3.isEmpty) {
            ilN = p :: ilN
          } else {
            val newITEVar = "FRESHv" + ic3
            icN = ic3 + 1
            ilN = il3 ::: ilN
            ilN = (newITEVar, TIte(fF, t1F, t2F)) :: ilN 
            addedFreshITEs = true
          }
        }
        case _ => error("Impossible case ")
      })
      flatten_ITEList(ilN, icN, addedFreshITEs)
    } else il
  }


  def flattenITEExpressions(f:QFPAFormula):(QFPAFormula, List[(String,TermQFPA)]) = {
    var variableCount = 0
    var iteList:List[(String,TermQFPA)] = Nil
    val (f1, vc1, iteList1) = flattenITEExpressionsFormula(f, variableCount, iteList)
    // every ITE is pulled out
    val toBeFlattened = true
    val iteListFinal = flatten_ITEList(iteList1, vc1, toBeFlattened)
    (f1, iteListFinal)
  }

// end

//--------------

//start: v - list of (complex) terms
// output: $1 - formula describing freshly introduced terms
  def flattenComplexTerms(v:List[TermQFPA]):(QFPAFormula,List[TermQFPA]) =  {
    var tc = 0
    var tempForm:QFPAFormula = QFPATrue
    var tempVector:List[TermQFPA] = Nil
    v.foreach(t => t match {
      case TVariable(v) => tempVector = t :: tempVector
      case TConstant(c) => tempVector = t :: tempVector
      case  _ => {
        val newTermVar = "FRESHt" + tc
        val fTemp = QFPAAtom(AEq(TVariable(newTermVar), t))
        tempForm = QFPAAnd(tempForm, fTemp)
        tempVector = TVariable(newTermVar) :: tempVector
        tc = tc + 1
      }
      })
    val fN = multisets.Multiset2StarsTranslator.removeTrueAndFalse(tempForm)
    val tN = tempVector.reverse
    (fN, tN)
  }
//end


// ------------
// start: input f AND l (l = list of conjunction of equlities about ITE)
//output: DNF of f AND f1 in form List[List[formula]]
  def nnform(f:QFPAFormula):QFPAFormula = f match {
    case QFPANot(QFPANot(f1)) => nnform(f1)
    case QFPANot(QFPAAnd(f1, f2)) => QFPAOr(QFPANot(nnform(f1)), QFPANot(nnform(f2)))
    case QFPANot(QFPAOr(f1, f2)) => QFPAAnd(QFPANot(nnform(f1)), QFPANot(nnform(f2)))
    case QFPAAnd(f1, f2) => QFPAAnd(nnform(f1), nnform(f2))
    case QFPAOr(f1, f2) => QFPAOr(nnform(f1), nnform(f2))
    case QFPANot(f1) => QFPANot(nnform(f1))
    case _ => f
  }

  def removeNegationFromNegatedAtom(a:AtomQFPA):QFPAFormula = a match {
    case ALeq(t1, t2) => QFPAAtom(ALeq(TPlus(t2, TConstant(1)), t1))
    case AEq(t1, t2) => QFPAOr(
      QFPAAtom(ALeq(TPlus(t1, TConstant(1)), t2)),
      QFPAAtom(ALeq(TPlus(t2, TConstant(1)), t1))
    )
  }

  def removeNegationCompletely(f:QFPAFormula):QFPAFormula = f match {
    case QFPAAnd(f1, f2) => QFPAAnd(removeNegationCompletely(f1), removeNegationCompletely(f2))
    case QFPAOr(f1, f2) => QFPAOr(removeNegationCompletely(f1), removeNegationCompletely(f2))
    case QFPANot(QFPAAtom(a)) => removeNegationFromNegatedAtom(a)
    case QFPANot(QFPATrue) => QFPAFalse
    case QFPANot(QFPAFalse) => QFPATrue
    case _ => f
  }


  def mergeTwoConjuntions(d1:List[QFPAFormula], d2:List[QFPAFormula]): List[List[QFPAFormula]] = {
    val ln = d1 ::: d2
    List(ln)
  }

  def addOneDisjuntToWholeFormula(l:List[List[QFPAFormula]], c:List[QFPAFormula]): List[List[QFPAFormula]] = {
    var lt: List[List[QFPAFormula]] = Nil
    l.foreach(s => {
      val fn = mergeTwoConjuntions(s, c)
      lt = fn ::: lt
    })
    lt
  }

  def mergeTwoDisjunctions(l1: List[List[QFPAFormula]], l2: List[List[QFPAFormula]]): List[List[QFPAFormula]] = {
    var lt: List[List[QFPAFormula]] = Nil
    l2.foreach(s => {
      val ln = addOneDisjuntToWholeFormula(l1, s)
      lt = ln ::: lt
    })
    lt
  }


  def disjuntiveNormalForm(f:QFPAFormula): List[List[QFPAFormula]] = {
    val f1 = nnform(f)
    val f2 = removeNegationCompletely(f1)
    val f3 = f2 match {
      case QFPAAnd(fa, fb) => {
        val f1N = disjuntiveNormalForm(fa)
        val f2N = disjuntiveNormalForm(fb)
        mergeTwoDisjunctions(f1N, f2N)
      }
      case QFPAOr(fa, fb) => {
        val f1N = disjuntiveNormalForm(fa)
        val f2N = disjuntiveNormalForm(fb)
        f1N ::: f2N
      }
      case  _ => List(List(f2))
    }
    f3
  }


// -------------------------


  def mergeTogether(c:List[QFPAFormula],f:List[List[QFPAFormula]]):List[List[QFPAFormula]] = {
    val list1 = f.map(d => c ::: d)
    list1
  }

  def addITEExpressionToOneDisjunct(c:List[QFPAFormula], p:(String,TermQFPA)): List[List[QFPAFormula]] = {
    val lN = p._2 match {
      case TIte(f, t1, t2) => {
         val f1 = disjuntiveNormalForm(f)
         val f2 = disjuntiveNormalForm(QFPANot(f))
         val c1 = QFPAAtom(AEq(TVariable(p._1), t1)) :: c
         val c2 = QFPAAtom(AEq(TVariable(p._1), t2)) :: c
         val l1 = mergeTogether(c1, f1)
         val l2 = mergeTogether(c2, f2)
         l1 ::: l2
      }
      case x@_ => error("Impossible case :" + x)
    }
    lN
  }

  def evaluateITEExpressionInListOfDisjunctions(l: List[List[QFPAFormula]], t:(String,TermQFPA)): List[List[QFPAFormula]] = {
    var lt: List[List[QFPAFormula]] = Nil
    l.foreach(s => {
      val ln = addITEExpressionToOneDisjunct(s, t)
      lt = ln ::: lt
    })
    lt
  }

  def unrollITEExpressions(f:QFPAFormula,lITE: List[(String,TermQFPA)]): List[List[QFPAFormula]] = {
    val fN = disjuntiveNormalForm(f)
    var lTemp = fN
    lITE.foreach(t => {
      val lNew = evaluateITEExpressionInListOfDisjunctions(lTemp, t)
      lTemp = lNew
    })
    lTemp
  }

// end





// ------------------

/// STRT: to be considered!

  def replaceInequalitiesWithEqualitiesinAtom(a:AtomQFPA, lc:Int):(AtomQFPA,Int) = a match {
     case ALeq(t1, t2) => {
     val newTermVar =  "FRESHl" + lc
     val newRHS = TPlus(t1, TVariable(newTermVar))
     (AEq(t2, newRHS), lc + 1)
    }
     case AEq(t1, t2) => (a, lc)
  }

  def replaceInequalitiesWithEqualitiesinOneSingleFormula(f:QFPAFormula, lc:Int):(QFPAFormula,Int) = f match {
    case QFPAAtom(a) => {
      val (a1, lc1) = replaceInequalitiesWithEqualitiesinAtom(a, lc)
      (QFPAAtom(a1), lc1)
    }
    case QFPATrue => (f, lc)
    case _ => error("Impossible case ")
  }

  def replaceInequalitiesWithEqualitiesinConjunct(l:List[QFPAFormula], lc:Int):(List[QFPAFormula],Int) = {
    var lc1 = lc
    var lTemp: List[QFPAFormula] = Nil
    l.foreach(f => {
      val (fT, lcT) = replaceInequalitiesWithEqualitiesinOneSingleFormula(f, lc1)
      lc1 = lcT
       lTemp = fT :: lTemp
    })
    (lTemp, lc1)
  }


  def replaceInequalitiesWithEqualities(l:List[List[QFPAFormula]]):List[List[QFPAFormula]] = {
    var lTemp: List[List[QFPAFormula]] = Nil
    var lc = 0
    l.foreach(c => {
      val (cT, lcT) = replaceInequalitiesWithEqualitiesinConjunct(c, lc)
      lc = lcT
      lTemp = cT :: lTemp
    })
    lTemp
  }

//// END

  def consistentConjunctUsingZ3(c:List[QFPAFormula]):Boolean = {
    val out = multisets.CheckingConsistency.callZ3toDetermineConsistency(c)
    val res = if (out == "sat") true else false
    res
  }

  def removeRedundantUsingZ3(c:List[QFPAFormula]):List[QFPAFormula] = {
    var l1: List[QFPAFormula] = Nil
    var l2 = c
    while (! l2.isEmpty) {
      val f = l2.head
      l2 = l2.tail
      if (consistentConjunctUsingZ3((QFPANot(f) :: l2) ::: l1) ) l1 = f :: l1
    }
    l1
  }

  def useAntisymmetryToDeriveEq(c:List[QFPAFormula]): List[QFPAFormula] = {
    var l1: List[QFPAFormula] = Nil
    var ltemp: List[QFPAFormula] = Nil
    var l2 = c
    while (! l2.isEmpty) {
      val f = l2.head
      l2 = l2.tail
      f match {
        case QFPAAtom(ALeq(t1, t2)) => {
          if (l2.exists(fl => fl == QFPAAtom(ALeq(t2, t1)))) ltemp = f :: ltemp
          else if (ltemp.exists(fl => fl == QFPAAtom(ALeq(t2, t1)))) l1 = QFPAAtom(AEq(t1, t2)) :: l1
          else l1 = f :: l1 
        }
        case _ => l1 = f :: l1 
      }
    }
    l1
  }

  def checkConsistencyAndRemoveRedundantUsingZ3(l:List[List[QFPAFormula]]): List[List[QFPAFormula]] = {
    var lTemp: List[List[QFPAFormula]] = Nil
    l.foreach(c => if (consistentConjunctUsingZ3(c)) {
      val c1 = removeRedundantUsingZ3(c)
      val c2 = useAntisymmetryToDeriveEq(c1)
     // a <= b & b <= a ===> a = b
      lTemp = c2 :: lTemp
    })
    lTemp
  }

// ----------------------

/*

  def checkIfTermIsAboutTempVVariable(t:TermQFPA):Boolean = t match {
    case TVariable(v) => v.startsWith("FRESHv")
    case TConstant(c) =>  false
    case TPlus(t1, t2) => false
    case TTimes(c, t1) => false
    case x@_ => error("Impossible case :" + x)
  }

  def isAtomAboutTempVVariable(a:AtomQFPA):Boolean = a match {
    case AEq(t1, t2) => checkIfTermIsAboutTempVVariable(t1)
    case x@_ => error("Impossible case :" + x)
  }

  def isFormulaAboutTempVVariable(f:QFPAFormula):Boolean = f match {
    case QFPAAtom(a) => isAtomAboutTempVVariable(a)
    case QFPAEmpty => false
    case QFPATrue => false
    case x@_ => error("Impossible case :" + x)
  }

  def separateEqualitiesIntoTwoListsDepandingOnTempVarV(c:List[QFPAFormula]):(List[QFPAFormula],List[QFPAFormula]) = {
    var l1T: List[QFPAFormula] = Nil
    var l2T: List[QFPAFormula] = Nil
    c.foreach(f => {
      if (isFormulaAboutTempVVariable(f)) {
        l2T = f :: l2T
      } else l1T = f :: l1T
    })
    (l1T, l2T)
  }


  def getStringValueofTempVarV(t:TermQFPA):String = t match {
    case TVariable(v) => v
    case x@_ => error("Impossible case :" + x)
  }

  def createValueOfTempVarVAtom(a:AtomQFPA):(String,TermQFPA) = a match {
    case AEq(t1, t2) => {
      val s = getStringValueofTempVarV(t1)
      (s, t2)
    }
    case x@_ => error("Impossible case :" + x)
  }

  def createValueOfTempVarV(f:QFPAFormula):(String,TermQFPA) = f match {
    case QFPAAtom(a) => createValueOfTempVarVAtom(a)
    case x@_ => error("Impossible case :" + x)
  }

   def updateValuesWitnNewVValueTerm(tt:TermQFPA, vu:String, tu: TermQFPA):TermQFPA = tt match {
    case TVariable(v) => if (v == vu) tu else tt
    case TConstant(c) =>  tt
    case TPlus(t1, t2) => {
      val t1N = updateValuesWitnNewVValueTerm(t1, vu, tu)
      val t2N = updateValuesWitnNewVValueTerm(t2, vu, tu)
      TPlus(t1N, t2N)
    }
    case TTimes(c, t1) => {
      val t1N = updateValuesWitnNewVValueTerm(t1, vu, tu)
      TTimes(c, t1N)
    }
    case x@_ => error("Impossible case :" + x)
  }

   def updateValuesWitnNewVValueAtom(a:AtomQFPA, v:String, t: TermQFPA):AtomQFPA = a match {
    case AEq(t1, t2) => {
      val t1N = updateValuesWitnNewVValueTerm(t1, v, t)
      val t2N = updateValuesWitnNewVValueTerm(t2, v, t)
      AEq(t1N, t2N)
    }
    case x@_ => error("Impossible case :" + x)
  }

   def updateValuesWitnNewVValueFormula(f:QFPAFormula, v:String, t: TermQFPA):QFPAFormula = f match {
    case QFPAAtom(a) => QFPAAtom(updateValuesWitnNewVValueAtom(a, v, t))
    case QFPAEmpty => f
    case QFPATrue => f
    case x@_ => error("Impossible case :" + x)
  }


   def updateValuesWitnNewVValue(l:List[QFPAFormula], v:String, t: TermQFPA):List[QFPAFormula] = {
    var lTemp: List[QFPAFormula] = Nil
    l.foreach(f => {
      val fN = updateValuesWitnNewVValueFormula(f, v, t)
      lTemp = fN :: lTemp
    })
    lTemp
  }


  def getRidOfTempVVariablesFromConjuntion(c:List[QFPAFormula]):List[QFPAFormula] = {
    val (l1, l2) = separateEqualitiesIntoTwoListsDepandingOnTempVarV(c)
    var l1T = l1
    var l2T = l2
    while (! l2T.isEmpty) {
      val (v, t) = createValueOfTempVarV(l2T.head)
      val lT = l2T.tail
      l1T = updateValuesWitnNewVValue(l1T, v, t)
      l2T = updateValuesWitnNewVValue(lT, v, t)
    } 
    l1T
  }

  def orientEqualities(c:List[QFPAFormula]):List[QFPAFormula] = {
    var l1: List[QFPAFormula] = Nil
    var l2 = c
    while (! l2.isEmpty) {
      val f = l2.head
      l2 = l2.tail
      f match {
        case QFPAAtom(AEq(t1, TVariable(v))) =>  l1 = QFPAAtom(AEq(TVariable(v), t1)) :: l1 
        case _ => l1 = f :: l1 
      }
    }
    l1
  }

  def getRidOfTempVVariablesandOrientEqualities(l:List[List[QFPAFormula]]):List[List[QFPAFormula]] = {
    var lTemp: List[List[QFPAFormula]] = Nil
    l.foreach(c => {
      val c1 = getRidOfTempVVariablesFromConjuntion(c)
      val c2 = orientEqualities(c1)
       lTemp = c2 :: lTemp
    })
    lTemp
  }

*/

  def getVariablesfromFormula(f:QFPAFormula):Set[String] = {
    val l1 = multisets.CheckingConsistency.getAllVariablesAndConstsFromFormula(f)
    l1._1
  } 

  def getvariablesFromVector(l:List[TermQFPA]):Set[String] = {
    var s1 = Set.empty[String]
    l.foreach(t => s1 = s1 ++ multisets.RemoveStars.getAllVariablesFromTerm(t))
    s1
  }

// start

  def createZeroMap(vars:Set[String]):Map[String,Int] = {
    var m = Map.empty[String,Int]
    vars.foreach(v => m += (v -> 0))
    m += ("CONST" -> 0)
    m
  }


  def addVariableinMap(v:String,vars:Set[String]):Map[String,Int] = {
    var m = createZeroMap(vars)
    m += (v -> 1)
    m
  }

  def addConstantInMap(c:Int,vars:Set[String]):Map[String,Int] = {
    var m = createZeroMap(vars)
    m += ("CONST" -> c)
    m
  }

  def sumTwoMaps(m1:Map[String,Int],m2:Map[String,Int],vars:Set[String]):Map[String,Int] = {
    var m3 = Map.empty[String,Int]
    vars.foreach(v => {
      val l = m1(v) + m2(v)
      m3 += (v -> l)
    })
    val c = m1("CONST") + m2("CONST") 
    m3 += ("CONST" -> c)
    m3
  }


  def multiplyMap(c:Int,m:Map[String,Int],vars:Set[String]):Map[String,Int] = {
    var mN = Map.empty[String,Int]
    vars.foreach(v => {
      val l = c * m(v)
      mN += (v -> l)
    })
    val cn = c * m("CONST") 
    mN += ("CONST" -> cn)
    mN
  }


  def createMapRepresentingTerm(t:TermQFPA,vars:Set[String]):Map[String,Int] = t match {
    case TVariable(v) => addVariableinMap(v,vars)
    case TConstant(c) => addConstantInMap(c,vars)
    case TPlus(t1, t2) => {
      val m1 = createMapRepresentingTerm(t1, vars)
      val m2 = createMapRepresentingTerm(t2, vars)
      sumTwoMaps(m1, m2, vars)
    }
    case TTimes(c, t1) => {
      val m1 = createMapRepresentingTerm(t1, vars)
      multiplyMap(c, m1, vars)
    }
    case x@_ => error("Impossible case :" + x)
  }

  def createMapRepresentingFormula(f:QFPAFormula,vars:Set[String]):(String,Map[String,Int]) = {
    val p = f match {
      case QFPAAtom(ALeq(t1, t2)) => {
        val s = "i"
        val m1 = createMapRepresentingTerm(t1, vars)
        val m2 = createMapRepresentingTerm(t2, vars)
        val m3 = multiplyMap(-1, m1, vars)
        val m = sumTwoMaps(m2, m3, vars)
        (s, m)
      }
      case QFPAAtom(AEq(t1, t2)) => {
        val s = "e"
        val m1 = createMapRepresentingTerm(t1, vars)
        val m2 = createMapRepresentingTerm(t2, vars)
        val m3 = multiplyMap(-1, m1, vars)
        val m = sumTwoMaps(m2, m3, vars)
        (s, m)
      }
      case QFPATrue => {
        val s = "t"
        val m = createZeroMap(vars)
        (s, m)
      }
      case x@_ => error("Impossible case :" + x)
   }
   p
  }

//  end

 
  def updateOneMapWithOther(mTU:Map[String,Int],m:Map[String,Int],v:String):Map[String,Int] = {
    val c = mTU(v)
    val j = m(v)
    val mT1 = mTU - v
    val m1 = m - v
//    val vars = m.keySet 
// hell:
    var vars = Set.empty[String]
    vars = vars ++ m1.keySet
    val m2 = if (j == 1) multiplyMap(-1,m1,vars) else m1
    val m3 = multiplyMap(c,m2,vars)
    sumTwoMaps(mT1, m3, vars)
  }

  def updateMapwhileQE(l:List[(String,Map[String,Int])],m:Map[String,Int],v:String):List[(String,Map[String,Int])] = {
    var lt = List.empty[(String,Map[String,Int])]
    l.foreach(p => {
      if (p._2 != m) {
        val m1 = updateOneMapWithOther(p._2, m, v)
        lt = (p._1, m1) :: lt
      }
    })
    lt
  }

  def eliminateVariable(v:String,l:List[(String,Map[String,Int])]):(List[(String,Map[String,Int])],Boolean) = {
    val lf = l.filter(p => p._1 == "e" && (p._2(v) == 1 || p._2(v) == -1))
    val res = if (lf.isEmpty) (l, false) else (updateMapwhileQE(l, lf.head._2, v), true)
    res
  }


  def createOneTermFromMap(i:Int,v:String,m:Map[String,Int]):TermQFPA = {
     val c = i * m(v)
     val t = if (v == "CONST") TConstant(c) else 
       if (c == 1) TVariable(v) else TTimes(c, TVariable(v))
     t
  }

  def constructTermFromMap(i:Int,vars:Set[String],m:Map[String,Int]):TermQFPA = {
    val t = if (vars.isEmpty) TConstant(0) else {
      val l = vars.toList
      var term = createOneTermFromMap(i, l.head, m)
      val ltail = l.tail
      ltail.foreach(v =>  {
        val t1 = createOneTermFromMap(i, v, m)
        term = TPlus(t1, term)
      })
      term
    }
    t
  }

  def constructPositiveTermFromMap(pVars:Set[String],m:Map[String,Int]):TermQFPA = 
   constructTermFromMap(1, pVars, m)

  def constructNegativeTermFromMap(nVars:Set[String],m:Map[String,Int]):TermQFPA =
    constructTermFromMap(-1, nVars, m)


  def getPositiveAndNegativeVarsandConstFromMap(m:Map[String,Int],vars:Set[String]):(Set[String],Set[String]) = {
    var sp = Set.empty[String]
    var sn = Set.empty[String]
    vars.foreach(v => {
      if (m(v) > 0) sp = sp + v
      if (m(v) < 0) sn = sn + v
    })
    if (m("CONST") > 0) sp = sp + "CONST"
    if (m("CONST") < 0) sn = sn + "CONST"
    (sp, sn)
  }


  def reconstructEqualityFromMap(m:Map[String,Int],vars:Set[String]):QFPAFormula = {
    val (pVars, nVars) = getPositiveAndNegativeVarsandConstFromMap(m, vars)
    val tp = constructPositiveTermFromMap(pVars, m)
    val tn = constructNegativeTermFromMap(nVars, m)
    QFPAAtom(AEq(tp, tn))
  }

  def reconstructInequalityFromMap(m:Map[String,Int],vars:Set[String]):QFPAFormula = {
    val (pVars, nVars) = getPositiveAndNegativeVarsandConstFromMap(m, vars)
    val tp = constructPositiveTermFromMap(pVars, m)
    val tn = constructNegativeTermFromMap(nVars, m)
    QFPAAtom(ALeq(tn, tp))
  }


  def reconstructFormulaFromMaps(t:(String,Map[String,Int]),vars:Set[String]):QFPAFormula = {
    val f = if (t._1 == "t") QFPATrue else
      if (t._1 == "e") reconstructEqualityFromMap(t._2,vars)
      else  reconstructInequalityFromMap(t._2,vars) 
    f
  }

  def reconstructFormulasFromMaps(l:List[(String,Map[String,Int])],vars:Set[String]):List[QFPAFormula] = {
    val list1 = l.map(e => reconstructFormulaFromMaps(e,vars))
    list1
  }



  def doSimpleQE(v:List[TermQFPA],l:List[QFPAFormula]):List[QFPAFormula] = {
   val inVars = getvariablesFromVector(v)
   var allVars = Set.empty[String]
   l.foreach(f => allVars = allVars ++ getVariablesfromFormula(f))
   val varsForQE = allVars -- inVars
   val listOfMaps = l.map(f => createMapRepresentingFormula(f, allVars))
   var fmla = listOfMaps
   var eliminated = Set.empty[String]
   varsForQE.foreach(v => {
      val p = eliminateVariable(v, fmla)
      fmla = p._1
      if (p._2) eliminated = eliminated + v
   })
   val l1 = reconstructFormulasFromMaps(fmla,allVars -- eliminated)
   l1
  } 


 // def doEliminationOfConstants(v:List[TermQFPA],List[



// -----------------------

  def main(v:List[TermQFPA],f:QFPAFormula): (List[TermQFPA], List[List[QFPAFormula]]) = {
    val (fTemp1, vN) = flattenComplexTerms(v)
    val fNew1 = if (fTemp1 == QFPATrue) f else QFPAAnd(f, fTemp1)
    val (fNew2, fl) = flattenITEExpressions(fNew1)
    // fNew2 is a formula that doesn't contain ITE expressions, 
    //fl is a list of a type (v, ITE(...)) no nested ITE expressions
    val listDNFNoITEs = unrollITEExpressions(fNew2, fl)
    // no more ITE expressions and listDNFNoITs is in DNF, does not contain ITEs
    // listDNFNoITEs is a list of lists of formulas
    val list1 = checkConsistencyAndRemoveRedundantUsingZ3(listDNFNoITEs)
    // list1 contains only satisfiable constraints
    val list2 = list1.map(f => doSimpleQE(vN,f))
    val list3 = replaceInequalitiesWithEqualities(list2)
/*    val list3 = getRidOfTempVVariablesandOrientEqualities(list2) */
     // a + b = c ===> c = a + b
    (vN, list3)
    // vN is a term that contains only variables and list1 is a list of lists of formulas
  }

}
