package multisets


object RemoveDisjunctions {

//

  def createListofFreshVectors(n:Int, m:Int): List[List[TermQFPA]] = {
    var i = 0
    var lOut: List[List[TermQFPA]] = Nil
    while (i < n) {
      var j = 0
      var  lIn: List[TermQFPA] = Nil
      while (j < m) {
        var num = i * m + j
        var newUVar = "FRESHu" + num
        var tmpTermVar = TVariable(newUVar)
        lIn = tmpTermVar :: lIn
        j += 1
      }
      var lInN = lIn.reverse
      lOut = lInN :: lOut
      i += 1
    }
    lOut
  }

  def createSumOfAllUVecs(i:Int, u:List[List[TermQFPA]]):TermQFPA = {
   val n = u.length
   var j = 0
   var tt = (u(j))(i)
   j += 1
   while (j < n) {
     var tn = (u(j))(i)
     tt = TPlus(tt, tn) 
     j += 1
   }
   tt
  }



  def createFormulaWithFreshUsVariables(u:List[TermQFPA], uVec:List[List[TermQFPA]]):QFPAFormula = {
    val m = u.length
    var j = 0
    var tR = createSumOfAllUVecs(j, uVec)
    var tL = u(j)
    var eq = AEq(tL, tR)
    var f:QFPAFormula = QFPAAtom(eq)
    j += 1
    while (j < m) {
      tR = createSumOfAllUVecs(j, uVec)
      tL = u(j)
      eq = AEq(tL, tR)
      f = QFPAAnd(f, QFPAAtom(eq))
      j += 1
    }
    f
  }


//-------------------------------------
// main creates List of LIAStar Formulas 
// input f0 AND u IN { v | lDNF} ^*
// output $1 AND List($2, $3, $4) where $2 IN { $3 | $4 } ^*


  def main (f0:QFPAFormula, u:List[TermQFPA], v:List[TermQFPA], lDNF:List[List[QFPAFormula]]):
   (QFPAFormula, List[(List[TermQFPA], List[TermQFPA], List[QFPAFormula])]) = {
    val n = lDNF.length
    val m = u.length
    val listofFreshUs = createListofFreshVectors(n, m)
    var i = 0
    var listLIAS: List[(List[TermQFPA], List[TermQFPA], List[QFPAFormula])] = Nil
    lDNF.foreach(c => {
      listLIAS = (listofFreshUs(i), v, c) :: listLIAS
      i += 1
    })
    val fPA = createFormulaWithFreshUsVariables(u, listofFreshUs)
    (QFPAAnd(f0, fPA), listLIAS)
  }
}

