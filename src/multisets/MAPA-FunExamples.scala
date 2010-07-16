package mapaFun

import mapaFun.MAPAFunFormulaPrinter._
import multisets.MultisetFormulaPrinter._


object MAPAFunExamples {

//    val m1 = MFMPlus(MFFunction("f", MFSetVar("D")), MFFunction("f", MFSetVar("F")))
    val m1 = MFMPlus(MFFunction("f", MFSetVar("A")), MFFunction("f", MFSetVar("E")))
    val a1 = MFMSetEqual(MFFunction("f", MFSUnion(MFSetVar("A"), MFSetVar("E"))), m1)
    val s1 = MFSIntersec(MFSetVar("A"), MFSetVar("E"))
    val f1 = MFAnd(MFAtom(MFSetEqual(s1, MFEmptySet)), MFNot(MFAtom(a1)))

//---------------
// the one from the VMCAI submission

    val f21 = MFAtom(MFSetSubset(MFSetVar("N"), MFSetVar("A")))
    val f22 = MFAtom(MFIntEqual(MFSCard(MFSetVar("T")), MFIntConst (1)))
    val f23 = MFAtom(MFSetEqual(MFSIntersec(MFSetVar("T"), MFSetVar("A")), MFEmptySet))
    val f24 = MFAtom(MFMSetEqual(MFFunction("d", MFSetVar("T")), MFMSetVar("E")))
    val f25 = MFAtom(MFMSetEqual(MFFunction("d", MFSetVar("N")), MFMSetVar("C")))
    val f26 = MFAtom(MFSetEqual(MFSUnion(MFSetVar("N"), MFSetVar("T")), MFSetVar("N1")))
    val f27 = MFAtom(MFMSetEqual(MFFunction("d", MFSetVar("N1")), MFMSetVar("C1")))
    val f28 = MFNot(MFAtom(MFIntLessEqual(MFMCard(MFMSetVar("C1")), MFIPlus(MFMCard(MFMSetVar("C")), MFIntConst (1)))))
    val f2 = MFAnd(MFAnd(MFAnd(f21, f22), MFAnd(f23, f24)), MFAnd(MFAnd(f25, f26), MFAnd(f27, f28)))

//---------------


    def run (name: String, f: MAPAFunFormula): Unit = {
      println("Formula " + name + ":")
      print_MAPAFunFormula(f)
      println("")
      println("---------------------")
      val f1n = mapaFun.SetExpansionAndCNF.noMoreSets(f)
      print_MAPAFunFormula(f1n)
      println("")
      println("---------------------")
      val f2n = mapaFun.FunctionElimination.noMoreFunctions(f1n)
      print_MAPAFunFormula(f2n)
      println("")
      println("---------------------")
      val f3n = mapaFun.MapaFunConversion.mapaFun2standardMAPA(f2n)
      print_multisetFormula(f3n)
      println("")
      println("---------------------")
      println("And now the original decision procedure:")
      println("---------------------")
//      guru.multisets.Examples.run("f", f3n)
      println("---------------------")
   }


// -----

  def runExamples() {
    run("f1", f1)
//    run("f2", f2)
  }


}


