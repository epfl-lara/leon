package multisets


import multisets.MultisetFormulaPrinter._
import multisets.StarFormulaPrinter._



object MAPARun {

// start: describes the execution of checking satisfiability of one formula
   def executeOneFormula (name: String, f: Formula): Boolean = {
      println("Formula " + name + ":")
      print_multisetFormula(f)
      println("")
      val (x, y, z) = multisets.NormalFormTranslator.main(f)
      val fF = FAnd(x, FAnd(y, z))
      println("Normalized formula " + name + ":")
      print_multisetFormula(fF)
      println("")
      val (fS1, lS1, lS2, fS2) = multisets.Multiset2StarsTranslator.main(x, y, z)
      val fS = StarFormula(fS1, lS1, lS2, fS2)
      println("Translated formula " + name + ":")
      print_starFormula(fS)
      println("")
      val (lS2N, listDNFfS2) = multisets.CreateDisjunctions.main(lS2, fS2)
      val (ff, lpf) = multisets.RemoveDisjunctions.main(fS1, lS1, lS2N, listDNFfS2)
      println("No more disjunctions:")
      print_QFPAFormula(ff)
      println(" AND " )
      lpf.foreach(t => { 
        print_PAVector(t._1)
        print( " IN { ")
        print_PAVector(t._2)
        print( " |  ")
        (t._3).foreach(c => {
          print_QFPAFormula(c)
          print(" AND ")
        })
        print( " } ^*  ")
        println(" AND " )
      })
      println("Semilinear set computation :")
      val ff1 = multisets.RemoveStars.removeStarsMain(ff, lpf)
      println("No more stars: ")
      print_QFPAFormula(ff1)
      val l = multisets.CheckingConsistency.checkConsistencyofOneFormula(ff1)
      val bs = l._1
      val b = if (bs == "sat") true else false
      println("")
      println("---------------------")
      if (b) {
        println ("This formula is " + bs)
        println("")
        println("---------------------")
/*        println("Here is the satisfying assignment:")
        val m1 = guru.multisets.reconstructingModels.createSatisfyingAssignmentforQFPA(l)
        println(m1)
        println("")
        println("After removing mu's and nu's : ")
        val ff1t = guru.multisets.reconstructingModels.evaluateFormulaForVariablesStartingWith(ff1, m1, "FRESHnu")
        val ff1s = guru.multisets.reconstructingModels.evaluateFormulaForVariablesStartingWith(ff1t, m1, "FRESHmu")
        print_QFPAFormula(ff1s)
        println("")
        println("")
        println("After removing obsolete disjuntions: ")
        var ff2s = ff1s
        var ltm: List[(List[TermQFPA], List[TermQFPA], List[QFPAFormula])] = Nil
        lpf.foreach(t => {
          if (guru.multisets.reconstructingModels.isNulVectorinGivenModel(t._1, m1)) {
             val ff3s = guru.multisets.reconstructingModels.removeZeroVectorInFormula(ff2s, t._1)
             ff2s = ff3s
          } else ltm = t :: ltm
        })
        print_QFPAFormula(ff2s)
        println("")
        println("")
        println("Star formulas and no disjunctions:")
        print_QFPAFormula(ff)
        println(" AND " )
        ltm.foreach(t => { 
          print_PAVector(t._1)
          print( " IN { ")
          print_PAVector(t._2)
          print( " |  ")
          (t._3).foreach(c => {
            print_QFPAFormula(c)
            print(" AND ")
          })
          print( " } ^*  ")
          println(" AND " )
        })
        println("")

        println("Introduce the real values of vectors : ")
        val ff4 = guru.multisets.reconstructingModels.evaluateFormulaForVariablesStartingWith(ff2s, m1, "FRESHu") 
        print_QFPAFormula(ff4) */
      } else { println("")
        println ("This formula is " + bs)
        println("")
        println("---------------------")
      }
      b
   }
// end



  def run(fileName: String): Unit = {
   val problemList = multisets.MAPAParser.main(fileName)
   val formulasList = multisets.FormulaConstructor.main(problemList)
   // all returned formulas are in NNF
   formulasList.foreach(p => {
     val flas = p._2
     val fOrig = flas._1
     val fOrigNeg = flas._2
     val fCons = flas._3
     val isValid = (executeOneFormula(p._1, FAnd(fOrigNeg, fCons)) == false)
     if (isValid) println("This means that the original problem " + p._1 + " is valid.") else {
       println("This was a model for the negated formula. Now we check the original formula:")
       val isUnsat = (executeOneFormula(p._1, FAnd(fOrig, fCons)) == false)
       if (isUnsat) println("This means, that the original problem " + p._1 + " is unsatisfiable.") else {
         println("This means that the original problem " + p._1 + " is satisfiable, but not valid.")
       }
     }
   })
 }



}