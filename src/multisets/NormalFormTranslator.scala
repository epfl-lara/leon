package multisets


import multisets.MultisetFormulaPrinter._


object NormalFormTranslator {



// start: this part extraxts all complex (diff. than a variable) expressions
//input: f - Formula, mc - counter for fresh, mm - list containing (var, Multiset)
//output : Formula - containing only variables as multisets, Int-counter  List - variable, multiset
  def extractMsetsExpr_termOut(t:TermOut, mc:Int, mm:List[(String,Multiset)]):(TermOut,Int,List[(String,Multiset)]) = t match {
    case TOConstant(c) => (TOConstant(c), mc, mm)
    case TOVariable(v) => (TOVariable(v), mc, mm)
    case TOCard(MVariable(m)) => (TOCard(MVariable(m)), mc, mm)
    case TOCard(m) => {
      val newMulVar = "FRESHm" + mc
      var mm1 = (newMulVar, m)  :: mm
      (TOCard(MVariable(newMulVar)), mc + 1, mm1)
    }
    case TOPlus(t1, t2) => {
      val (t1n, mc1, mm1) = extractMsetsExpr_termOut(t1, mc, mm)
      val (t2n, mc2, mm2) = extractMsetsExpr_termOut(t2, mc1, mm1)
      (TOPlus(t1n, t2n), mc2, mm2)
    }
    case TOTimes(c, t1)=> {
      val (t1n, mc1, mm1) = extractMsetsExpr_termOut(t1, mc, mm)
      (TOTimes(c, t1n), mc1, mm1)
    }
    case TOIte(f, t1, t2)=> {
      val (f1, mc1, mm1) = extractMsetsExpr_formulaOut(f, mc, mm)
      val (t1n, mc2, mm2) = extractMsetsExpr_termOut(t1, mc1, mm1)
      val (t2n, mc3, mm3) = extractMsetsExpr_termOut(t2, mc2, mm2)
      (TOIte(f1,t1n, t2n), mc3, mm3)
    }
  }

  def extractMsetsExpr_atomOut(a:AtomOut, mc:Int, mm:List[(String,Multiset)]):(AtomOut,Int,List[(String,Multiset)]) = a match {
    case AOLeq(t1,t2) => {
      val (t1n, mc1, mm1) = extractMsetsExpr_termOut(t1, mc, mm)
      val (t2n, mc2, mm2) = extractMsetsExpr_termOut(t2, mc1, mm1)
      (AOLeq(t1n, t2n), mc2, mm2)
    }
    case AOEq(t1,t2) => {
      val (t1n, mc1, mm1) = extractMsetsExpr_termOut(t1, mc, mm)
      val (t2n, mc2, mm2) = extractMsetsExpr_termOut(t2, mc1, mm1)
      (AOEq(t1n, t2n), mc2, mm2)
    }
    case AOSum(l1, f, l2) => {
      var l3: List[TermOut] = Nil
      var mcN = mc
      var mmN = mm
      l1.foreach(t => {
        val (t1, mc1, mm1) = extractMsetsExpr_termOut(t, mcN, mmN)
        l3 = t1 :: l3 
        mcN = mc1
        mmN = mm1
      })
      (AOSum(l3.reverse, f, l2), mcN, mmN)
    }
  }

  def extractMsetsExpr_formulaOut(f:FormulaOut, mc:Int, mm:List[(String,Multiset)]):(FormulaOut,Int,List[(String,Multiset)]) = f match {
    case FOAnd(f1,f2) => {
	val (f1n, mc1, mm1) = extractMsetsExpr_formulaOut(f1, mc, mm)
	val (f2n, mc2, mm2) = extractMsetsExpr_formulaOut(f2, mc1, mm1)
	(FOAnd(f1n, f2n), mc2, mm2)
    }
    case FOOr(f1,f2) => {
	val (f1n, mc1, mm1) = extractMsetsExpr_formulaOut(f1, mc, mm)
	val (f2n, mc2, mm2) = extractMsetsExpr_formulaOut(f2, mc1, mm1)
	(FOOr(f1n, f2n), mc2, mm2)
    }
    case FONot(f1)  => {
      val (f1n, mc1, mm1) = extractMsetsExpr_formulaOut(f1, mc, mm)
      (FONot(f1n), mc1, mm1)
    }
    case FOAtom(a)  => {
     val (a1, mc1, mm1) = extractMsetsExpr_atomOut(a, mc, mm)
     (FOAtom(a1), mc1, mm1)
    }
    case FOTrue => (f, mc, mm)
    case FOFalse => (f, mc, mm)
  }

  def extractMsetsExpr_atom(a:Atom, mc:Int, mm:List[(String,Multiset)]):(Atom,Int,List[(String,Multiset)]) = a match {
    case AEqual(MVariable(v1),MVariable(v2)) => (AEqual(MVariable(v1),MVariable(v2)), mc, mm)
    case AEqual(MVariable(v1),m2) => {
      val newMulVar = "FRESHm" + mc
      var mm1 = (newMulVar, m2)  :: mm
      (AEqual(MVariable(v1),MVariable(newMulVar)), mc + 1, mm1)
    }
    case AEqual(m1, MVariable(v2)) => {
      val newMulVar = "FRESHm" + mc
      var mm1 = (newMulVar, m1)  :: mm
      (AEqual(MVariable(newMulVar),MVariable(v2)), mc + 1, mm1)
    }
    case AEqual(m1,m2) => {
      val newMulVar1 = "FRESHm" + mc
      var mm1 = (newMulVar1, m1)  :: mm
      val mcN = mc + 1
      val newMulVar2 = "FRESHm" + mcN
      var mm2 = (newMulVar2, m2)  :: mm1
      (AEqual(MVariable(newMulVar1),MVariable(newMulVar2)), mcN + 1, mm2)
    }
    case ASubset(MVariable(v1),MVariable(v2)) => (ASubset(MVariable(v1),MVariable(v2)), mc, mm)
    case ASubset(MVariable(v1),m2) => {
      val newMulVar = "FRESHm" + mc
      var mm1 = (newMulVar, m2)  :: mm
      (ASubset(MVariable(v1),MVariable(newMulVar)), mc + 1, mm1)
    }
    case ASubset(m1, MVariable(v2)) => {
      val newMulVar = "FRESHm" + mc
      var mm1 = (newMulVar, m1)  :: mm
      (ASubset(MVariable(newMulVar),MVariable(v2)), mc + 1, mm1)
    }
    case ASubset(m1,m2) => {
      val newMulVar1 = "FRESHm" + mc
      var mm1 = (newMulVar1, m1)  :: mm
      val mcN = mc + 1
      val newMulVar2 = "FRESHm" + mcN
      var mm2 = (newMulVar2, m2)  :: mm1
      (ASubset(MVariable(newMulVar1),MVariable(newMulVar2)), mcN + 1, mm2)
    }
    case AForAllElem(f) => (AForAllElem(f), mc, mm)
    case AAtomOut(a1)  => {
     val (a2, mc1, mm1) = extractMsetsExpr_atomOut(a1, mc, mm)
     (AAtomOut(a2), mc1, mm1)
    }
  }

  def extractMsetsExpr_formula(f:Formula, mc:Int, mm:List[(String,Multiset)]):(Formula,Int,List[(String,Multiset)]) = f match {
    case FAnd(f1,f2) => {
	val (f1n, mc1, mm1) = extractMsetsExpr_formula(f1, mc, mm)
	val (f2n, mc2, mm2) = extractMsetsExpr_formula(f2, mc1, mm1)
	(FAnd(f1n, f2n), mc2, mm2)
    }
    case FOr(f1,f2) => {
	val (f1n, mc1, mm1) = extractMsetsExpr_formula(f1, mc, mm)
	val (f2n, mc2, mm2) = extractMsetsExpr_formula(f2, mc1, mm1)
	(FOr(f1n, f2n), mc2, mm2)
    }
    case FNot(f1)  => {
      val (f1n, mc1, mm1) = extractMsetsExpr_formula(f1, mc, mm)
      (FNot(f1n), mc1, mm1)
    }
    case FAtom(a)  => {
     val (a1, mc1, mm1) = extractMsetsExpr_atom(a, mc, mm)
     (FAtom(a1), mc1, mm1)
    }
    case FTrue  => (f, mc, mm)
    case FFalse => (f, mc, mm)
  }
// end 


// start: list(var, multiset), can contain complex multiset expressions
// output: list(var, multiset), simple multiset expressions
  def flatten_multisetList(mc:Int, mm:List[(String,Multiset)], toBeChecked: Boolean):List[(String,Multiset)] = {
    var addedFreshMultisets = false
    var ml: List[(String,Multiset)] = Nil
    var mc1 = mc
    if (toBeChecked) {
      mm.foreach(p => p._2 match {
         case MVariable(v) => ml = p :: ml
         case MEmpty =>  ml = p :: ml
         case MUnion(MVariable(v1),MVariable(v2)) =>  ml = p :: ml
         case MUnion(MVariable(v1),m2) => {
           val newMulVar = "FRESHm" + mc1
           ml = (p._1, MUnion(MVariable(v1),MVariable(newMulVar))) :: ((newMulVar, m2)  :: ml)
           mc1 = mc1 + 1
           addedFreshMultisets = true
         }
         case MUnion(m1,MVariable(v2)) => {
           val newMulVar = "FRESHm" + mc1
           ml = (p._1, MUnion(MVariable(newMulVar),MVariable(v2))) :: ((newMulVar, m1)  :: ml)
           mc1 = mc1 + 1
           addedFreshMultisets = true
         }
         case MUnion(m1,m2) => {
           val newMulVar1 = "FRESHm" + mc1
           ml = (newMulVar1, m1)  :: ml
           mc1 = mc1 + 1
           val newMulVar2 = "FRESHm" + mc1
           ml = (newMulVar2, m2)  :: ml
           mc1 = mc1 + 1
           ml = (p._1, MUnion(MVariable(newMulVar1),MVariable(newMulVar2))) :: ml
           addedFreshMultisets = true
         }
         case MIntersection(MVariable(v1),MVariable(v2)) => ml = p :: ml
         case MIntersection(MVariable(v1),m2) => {
           val newMulVar = "FRESHm" + mc1
           ml = (p._1, MIntersection(MVariable(v1),MVariable(newMulVar))) :: ((newMulVar, m2)  :: ml)
           mc1 = mc1 + 1
           addedFreshMultisets = true
         }
         case MIntersection(m1,MVariable(v2)) => {
           val newMulVar = "FRESHm" + mc1
           ml = (p._1, MIntersection(MVariable(newMulVar),MVariable(v2))) :: ((newMulVar, m1)  :: ml)
           mc1 = mc1 + 1
           addedFreshMultisets = true
         }
         case MIntersection(m1,m2) => {
           val newMulVar1 = "FRESHm" + mc1
           ml = (newMulVar1, m1)  :: ml
           mc1 = mc1 + 1
           val newMulVar2 = "FRESHm" + mc1
           ml = (newMulVar2, m2)  :: ml
           mc1 = mc1 + 1
           ml = (p._1, MIntersection(MVariable(newMulVar1),MVariable(newMulVar2))) :: ml
           addedFreshMultisets = true
         }
         case MPlus(MVariable(v1),MVariable(v2)) => ml = p :: ml
         case MPlus(MVariable(v1),m2) => {
           val newMulVar = "FRESHm" + mc1
           ml = (p._1, MPlus(MVariable(v1),MVariable(newMulVar))) :: ((newMulVar, m2)  :: ml)
           mc1 = mc1 + 1
           addedFreshMultisets = true
         }
         case MPlus(m1,MVariable(v2)) => {
           val newMulVar = "FRESHm" + mc1
           ml = (p._1, MPlus(MVariable(newMulVar),MVariable(v2))) :: ((newMulVar, m1)  :: ml)
           mc1 = mc1 + 1
           addedFreshMultisets = true
         }
         case MPlus(m1,m2) => {
           val newMulVar1 = "FRESHm" + mc1
           ml = (newMulVar1, m1)  :: ml
           mc1 = mc1 + 1
           val newMulVar2 = "FRESHm" + mc1
           ml = (newMulVar2, m2)  :: ml
           mc1 = mc1 + 1
           ml = (p._1, MPlus(MVariable(newMulVar1),MVariable(newMulVar2))) :: ml
           addedFreshMultisets = true
         }
         case MMinus(MVariable(v1),MVariable(v2)) => ml = p :: ml 
         case MMinus(MVariable(v1),m2) => {
           val newMulVar = "FRESHm" + mc1
           ml = (p._1, MMinus(MVariable(v1),MVariable(newMulVar))) :: ((newMulVar, m2)  :: ml)
           mc1 = mc1 + 1
           addedFreshMultisets = true
         }
         case MMinus(m1,MVariable(v2)) => {
           val newMulVar = "FRESHm" + mc1
           ml = (p._1, MMinus(MVariable(newMulVar),MVariable(v2))) :: ((newMulVar, m1)  :: ml)
           mc1 = mc1 + 1
           addedFreshMultisets = true
         }
         case MMinus(m1,m2) => {
           val newMulVar1 = "FRESHm" + mc1
           ml = (newMulVar1, m1)  :: ml
           mc1 = mc1 + 1
           val newMulVar2 = "FRESHm" + mc1
           ml = (newMulVar2, m2)  :: ml
           mc1 = mc1 + 1
           ml = (p._1, MMinus(MVariable(newMulVar1),MVariable(newMulVar2))) :: ml
           addedFreshMultisets = true
         }
         case MSetMinus(MVariable(v1),MVariable(v2)) => ml = p :: ml 
         case MSetMinus(MVariable(v1),m2) => {
           val newMulVar = "FRESHm" + mc1
           ml = (p._1, MSetMinus(MVariable(v1),MVariable(newMulVar))) :: ((newMulVar, m2)  :: ml)
           mc1 = mc1 + 1
           addedFreshMultisets = true
         }
         case MSetMinus(m1,MVariable(v2)) => {
           val newMulVar = "FRESHm" + mc1
           ml = (p._1, MSetMinus(MVariable(newMulVar),MVariable(v2))) :: ((newMulVar, m1)  :: ml)
           mc1 = mc1 + 1
           addedFreshMultisets = true
         }
         case MSetMinus(m1,m2) => {
           val newMulVar1 = "FRESHm" + mc1
           ml = (newMulVar1, m1)  :: ml
           mc1 = mc1 + 1
           val newMulVar2 = "FRESHm" + mc1
           ml = (newMulVar2, m2)  :: ml
           mc1 = mc1 + 1
           ml = (p._1, MSetMinus(MVariable(newMulVar1),MVariable(newMulVar2))) :: ml
           addedFreshMultisets = true
         }
         case MSetOf(MVariable(v)) => ml = p :: ml  
         case MSetOf(m) => {
           val newMulVar = "FRESHm" + mc1
           ml = (newMulVar, m)  :: ml
           mc1 = mc1 + 1
           ml = (p._1, MSetOf(MVariable(newMulVar))) :: ml
           addedFreshMultisets = true
         }
      })
      flatten_multisetList(mc1, ml, addedFreshMultisets)
    }
    else mm
  }
// end



// start: input list(string, multiset) (m1, m2 un m3),...
// output: formula: Forall e.(m1 (e) = ... AND ..)
  def createFormulafromPair(p:(String,Multiset)):FormulaIn = p._2 match {
    case MEmpty => 
      FIAtom(AIEq(TIMultiplicity(p._1),TIConstant(0)))
    case MUnion(MVariable(v1),MVariable(v2)) => 
      FIAtom(AIEq(TIMultiplicity(p._1),
        TIIte(FIAtom(AILeq(TIMultiplicity(v1),TIMultiplicity(v2))), TIMultiplicity(v2), TIMultiplicity(v1))))
    case MIntersection(MVariable(v1),MVariable(v2)) => 
      FIAtom(AIEq(TIMultiplicity(p._1),
        TIIte(FIAtom(AILeq(TIMultiplicity(v1),TIMultiplicity(v2))), TIMultiplicity(v1), TIMultiplicity(v2))))
    case MPlus(MVariable(v1),MVariable(v2)) => 
      FIAtom(AIEq(TIMultiplicity(p._1),
        TIPlus(TIMultiplicity(v1), TIMultiplicity(v2))))
    case MMinus(MVariable(v1),MVariable(v2)) => 
      FIAtom(AIEq(TIMultiplicity(p._1),
        TIIte(FIAtom(AILeq(TIMultiplicity(v1),TIMultiplicity(v2))), TIConstant(0), 
        TIPlus(TIMultiplicity(v1), TITimes(-1, TIMultiplicity(v2))))))
    case MSetMinus(MVariable(v1),MVariable(v2)) => 
      FIAtom(AIEq(TIMultiplicity(p._1),
        TIIte(FIAtom(AIEq(TIMultiplicity(v2),TIConstant(0))), TIMultiplicity(v1), TIConstant(0))))
    case MSetOf(MVariable(v)) => 
      FIAtom(AIEq(TIMultiplicity(p._1),
        TIIte(FIAtom(AILeq(TIConstant(1),TIMultiplicity(v))), TIConstant(1), TIConstant(0))))
    case _ => error("Impossible case, canot get this here, but got " + p)
    }

  def createFormulafromMultisetList(mlist:List[(String,Multiset)]):Formula = {
    if (mlist.isEmpty) FAtom(AForAllElem(FITrue)) else {
      val firstPair = mlist.head
      val theRest = mlist.tail
      var fN = createFormulafromPair(firstPair)
      theRest.foreach(p => {
        val f = createFormulafromPair(p)
        fN = FIAnd(fN, f)
      })
      FAtom(AForAllElem(fN))
    } 
  } 
// end


// start: formula with m1 SUB m2 and m1 = m2
// output formula with forall e. m1(e) <= m2(e) and m1(e) = m2(e)
  def redefineMultisetAtom(a:Atom):Formula = a match {
    case AEqual(MVariable(v1),MVariable(v2)) => 
      FAtom(AForAllElem(FIAtom(AIEq(TIMultiplicity(v1), TIMultiplicity(v2)))))
    case ASubset(MVariable(v1),MVariable(v2)) => 
      FAtom(AForAllElem(FIAtom(AILeq(TIMultiplicity(v1), TIMultiplicity(v2)))))
    case AForAllElem(f) => FAtom(AForAllElem(f))
    case AAtomOut(a1)  => FAtom(AAtomOut(a1))
    case _ => error("Impossible case ")
  }

  def redefineMultisetAtoms(f:Formula):Formula = f match {
    case FAnd(f1,f2) => {
	val f1n = redefineMultisetAtoms(f1)
	val f2n = redefineMultisetAtoms(f2)
	FAnd(f1n, f2n)
    }
    case FOr(f1,f2) => {
	val f1n = redefineMultisetAtoms(f1)
	val f2n = redefineMultisetAtoms(f2)
	FOr(f1n, f2n)
    }
    case FNot(f1)  => {
      val f1n = redefineMultisetAtoms(f1)
      FNot(f1n)
    }
    case FAtom(a)  => {
     val a1 = redefineMultisetAtom(a)
     a1
    }
    case FTrue => f
    case FFalse => f
  }
// end


// start: input formula with cardinalities
// output: new formula where each cardinality is replaced with a fresh int var + List(intVar, msetVar) <-both strings 

  def extractCardExpr_termOut(t:TermOut, ic:Int, cl:List[(String,String)]):(TermOut,Int,List[(String,String)]) = t match {
    case TOConstant(c) => (TOConstant(c), ic, cl)
    case TOVariable(v) => (TOVariable(v), ic, cl)
    case TOCard(MVariable(m)) => {
      val newIntVar = "FRESHk" + ic
      var cl1 = (newIntVar, m)  :: cl
      (TOVariable(newIntVar), ic + 1, cl1)
    }
    case TOPlus(t1, t2) => {
      val (t1n, ic1, cl1) = extractCardExpr_termOut(t1, ic, cl)
      val (t2n, ic2, cl2) = extractCardExpr_termOut(t2, ic1, cl1)
      (TOPlus(t1n, t2n), ic2, cl2)
    }
    case TOTimes(c, t1)=> {
      val (t1n, ic1, cl1) = extractCardExpr_termOut(t1, ic, cl)
      (TOTimes(c, t1n), ic1, cl1)
    }
    case TOIte(f, t1, t2)=> {
      val (f1, ic1, cl1) = extractCardExpr_formulaOut(f, ic, cl)
      val (t1n, ic2, cl2) = extractCardExpr_termOut(t1, ic1, cl1)
      val (t2n, ic3, cl3) = extractCardExpr_termOut(t2, ic2, cl2)
      (TOIte(f1,t1n, t2n), ic3, cl3)
    }
    case _ => error("Impossible case ")
  }

  def extractCardExpr_atomOut(a:AtomOut, ic:Int, cl:List[(String,String)]):(AtomOut,Int,List[(String,String)]) = a match {
    case AOLeq(t1,t2) => {
      val (t1n, ic1, cl1) = extractCardExpr_termOut(t1, ic, cl)
      val (t2n, ic2, cl2) = extractCardExpr_termOut(t2, ic1, cl1)
      (AOLeq(t1n, t2n), ic2, cl2)
    }
    case AOEq(t1,t2) => {
      val (t1n, ic1, cl1) = extractCardExpr_termOut(t1, ic, cl)
      val (t2n, ic2, cl2) = extractCardExpr_termOut(t2, ic1, cl1)
      (AOEq(t1n, t2n), ic2, cl2)
    }
    case AOSum(l1, f, l2) => {
      var l3: List[TermOut] = Nil
      var icN = ic
      var clN = cl
      l1.foreach(t => {
        val (t1, ic1, cl1) = extractCardExpr_termOut(t, icN, clN)
        l3 = t1 :: l3 
        icN = ic1
        clN = cl1
      })
      (AOSum(l3.reverse, f, l2), icN, clN)
    }
  }

  def extractCardExpr_formulaOut(f:FormulaOut, ic:Int, cl:List[(String,String)]):(FormulaOut,Int,List[(String,String)]) = f match {
    case FOAnd(f1,f2) => {
	val (f1n, ic1, cl1) = extractCardExpr_formulaOut(f1, ic, cl)
	val (f2n, ic2, cl2) = extractCardExpr_formulaOut(f2, ic1, cl1)
	(FOAnd(f1n, f2n), ic2, cl2)
    }
    case FOOr(f1,f2) => {
	val (f1n, ic1, cl1) = extractCardExpr_formulaOut(f1, ic, cl)
	val (f2n, ic2, cl2) = extractCardExpr_formulaOut(f2, ic1, cl1)
	(FOOr(f1n, f2n), ic2, cl2)
    }
    case FONot(f1)  => {
      val (f1n, ic1, cl1) = extractCardExpr_formulaOut(f1, ic, cl)
      (FONot(f1n), ic1, cl1)
    }
    case FOAtom(a)  => {
     val (a1, ic1, cl1) = extractCardExpr_atomOut(a, ic, cl)
     (FOAtom(a1), ic1, cl1)
    }
    case FOTrue => (f, ic, cl)
    case FOFalse => (f, ic, cl)
  }


  def extractCardExpr_atom(a:Atom, ic:Int, cl:List[(String,String)]):(Atom,Int,List[(String,String)]) = a match {
    case AEqual(m1,m2) => (AEqual(m1,m2), ic, cl)
    case ASubset(m1,m2) => (ASubset(m1,m2), ic, cl)
    case AForAllElem(f) => (AForAllElem(f), ic, cl)
    case AAtomOut(a1)  => {
     val (a2, ic1, cl1) = extractCardExpr_atomOut(a1, ic, cl)
     (AAtomOut(a2), ic1, cl1)
    }
  }

  def extractCardExpr_formula(f:Formula, ic:Int, cl:List[(String,String)]):(Formula,Int,List[(String,String)]) = f match {
    case FAnd(f1,f2) => {
	val (f1n, ic1, cl1) = extractCardExpr_formula(f1, ic, cl)
	val (f2n, ic2, cl2) = extractCardExpr_formula(f2, ic1, cl1)
	(FAnd(f1n, f2n), ic2, cl2)
    }
    case FOr(f1,f2) => {
	val (f1n, ic1, cl1) = extractCardExpr_formula(f1, ic, cl)
	val (f2n, ic2, cl2) = extractCardExpr_formula(f2, ic1, cl1)
	(FOr(f1n, f2n), ic2, cl2)
    }
    case FNot(f1)  => {
      val (f1n, ic1, cl1) = extractCardExpr_formula(f1, ic, cl)
      (FNot(f1n), ic1, cl1)
    }
    case FAtom(a)  => {
     val (a1, ic1, cl1) = extractCardExpr_atom(a, ic, cl)
     (FAtom(a1), ic1, cl1)
    }
    case FTrue => (f, ic, cl)
    case FFalse => (f, ic, cl)
  }
// end 

// start: input list(var, mset), output: (var) = SUM_{} mset
  def createFormulafromCardinalityList(cl:List[(String,String)]):Formula = {
  var l1: List[TermOut] = Nil
  var l2: List[TermIn] = Nil
  if (cl.isEmpty) FAtom(AAtomOut(AOSum(List(TOConstant(0)), FITrue, List(TIConstant(0))))) else {
    cl.foreach(p => {
      l1 = TOVariable(p._1) :: l1
      l2 = TIMultiplicity(p._2) :: l2 
     })
     FAtom(AAtomOut((AOSum(l1, FITrue, l2))))
   }
  }

// end 


// start
// input: f- formula, fFA - allready existing formula of the form forall e.f(e)
//output:  $1 - formula without top-level forall, $2-forall e. f(e)
  def uniteForAll(fI:FormulaIn,f:Formula):Formula = f match {
    case FAtom(AForAllElem(f1))  => {
      val fn = if (f1 == FITrue) fI else FIAnd(fI, f1)
      FAtom(AForAllElem(fn))
    }
    case _ => error("Impossible case ")
  }


  def topLevelForAll(f:Formula,fFA:Formula):(Formula,Formula) = f match {
    case FAnd(FAtom(AForAllElem(fI)),f2) => {
       val (f2N, fFAN) = topLevelForAll(f2, fFA)
       (f2N, uniteForAll(fI, fFAN))
    }
    case FAnd(f1, FAtom(AForAllElem(fI))) => {
       val (f1N, fFAN) = topLevelForAll(f1, fFA)
       (f1N, uniteForAll(fI, fFAN))
    }
    case FAnd(f1,f2) => {
	val (f1n, fFA1) = topLevelForAll(f1, fFA)
	val (f2n, fFA2) = topLevelForAll(f2, fFA1)
        val f3n = if (f1n == FTrue) f2n else
          if (f2n == FTrue) f1n else FAnd(f1n, f2n)
	(f3n, fFA2)
    }
    case FOr(f1,f2) => (f, fFA)
    case FNot(f1)  => (f, fFA)
    case FAtom(AForAllElem(fI))  =>  (FTrue, uniteForAll(fI, fFA))
    case FAtom(a)  => (f, fFA)
    case FTrue => (f, fFA)
    case FFalse => (f, fFA)
  }
// end


// start
// input formula f - output f1 where every forall e. f is replaced with a sum: 
// forall e. f(e)  <=> 0 = sum_{true} ite(f(e); 0, 1)
  def replaceForAllWithSums(f:Formula):Formula = f match {
    case FAnd(f1,f2) => {
      val f1n = replaceForAllWithSums(f1)
      val f2n = replaceForAllWithSums(f2)
      FAnd(f1n, f2n)
    }
    case FOr(f1,f2) => {
      val f1n = replaceForAllWithSums(f1)
      val f2n = replaceForAllWithSums(f2)
      FOr(f1n, f2n)
    }
    case FNot(f1)  => {
      val f1n = replaceForAllWithSums(f1)
      FNot(f1n)
    }
    case FAtom(AForAllElem(f1))  => 
      FAtom(AAtomOut(AOSum(List(TOConstant(0)), FITrue, List(TIIte(f1,TIConstant(0),TIConstant(1))))))
    case FAtom(a)  => f
    case FTrue => f
    case FFalse => f
  }

  def notTopLevelForAll(f:Formula):Formula = f match {
    case FAnd(f1,f2) => {
      val f1n = notTopLevelForAll(f1)
      val f2n = notTopLevelForAll(f2)
     FAnd(f1n, f2n)
    }
    case FOr(f1,f2) => {
      val f1n = replaceForAllWithSums(f1)
      val f2n = replaceForAllWithSums(f2)
     FOr(f1n, f2n)
    }
    case FNot(f1)  => FNot(replaceForAllWithSums(f1))
    case FAtom(a)  => f
    case FTrue  => f
    case FFalse  => f
  }
// end



// start: input formula f and fS which is already a sum atom
// output: $1 without top level sums, $2 is a sum atom
  def eliminateConditions(f:FormulaIn, lIn: List[TermIn]):List[TermIn] = {
    var ltemp: List[TermIn] = Nil
    lIn.foreach(t => {
       val t1 = TIIte(f, t, TIConstant(0))
       ltemp = t1 :: ltemp
    })
    ltemp.reverse
  }


  def uniteSums(lTO:List[TermOut], lTI: List[TermIn], fD:FormulaIn,f:Formula):Formula = f match {
    case FAtom(AAtomOut(AOSum(lT0o, FITrue, lTIo)))  => fD match {
      case FITrue => FAtom(AAtomOut(AOSum(lTO ::: lT0o, FITrue, lTI ::: lTIo)))
      case _ => {
        val ltN = eliminateConditions(fD, lTI)
        FAtom(AAtomOut(AOSum(lTO ::: lT0o, FITrue, ltN ::: lTIo)))
      }
    }  
    case _ => error("Impossible case ")
  }

  def topLevelSums(f:Formula,fS:Formula):(Formula,Formula) = f match {
    case FAnd(FAtom(AAtomOut(AOSum(lTO, ff, lTI))), f2) => {
       val (f2N, fSN) = topLevelSums(f2, fS)
       (f2N, uniteSums(lTO, lTI, ff, fSN))
    }
    case FAnd(f1, FAtom(AAtomOut(AOSum(lTO, ff, lTI)))) => {
       val (f1N, fSN) = topLevelSums(f1, fS)
       (f1N, uniteSums(lTO, lTI, ff, fSN))
    }
    case FAnd(f1,f2) => {
	val (f1n, fS1) = topLevelForAll(f1, fS)
	val (f2n, fS2) = topLevelForAll(f2, fS1)
        val f3n = if (f1n == FTrue) f2n else
          if (f2n == FTrue) f1n else FAnd(f1n, f2n)
	(f3n, fS2)
    }
    case FOr(f1,f2) => (f, fS)
    case FNot(f1)  => (f, fS)
    case FAtom(AAtomOut(AOSum(lTO, ff, lTI)))  =>  (FTrue, uniteSums(lTO, lTI, ff, fS))
    case FAtom(a)  => (f, fS)
    case FTrue  => (f, fS)
    case FFalse  => (f, fS)
  }
// end


// start: input f - formula fs- sum atom, sc -counter
// outputs: $1 - formula without sums, $s2 - sum atom $3 -counter
  def createEqualityAtom(to:TermOut, sc:Int):(Atom,TermOut,Int) = {
    val newVar = "FRESHs" + sc
    val scN = sc + 1
    val a = AAtomOut(AOEq(to, TOVariable(newVar)))
    (a, TOVariable(newVar), scN)
  } 

  def createEqualityFormula(lTO:List[TermOut], sc:Int):(Formula,List[TermOut],Int) = {
    var tList: List[TermOut] = Nil
    val t1 = lTO.head
    val theRest = lTO.tail
    var (aN, vN, scN) = createEqualityAtom(t1, sc)
    var fN : Formula = FAtom(aN)
    tList = vN :: tList
    theRest.foreach(t => {
      val (aN1, vN1, scN1) = createEqualityAtom(t, scN)
      scN = scN1
      fN = FAnd(fN, FAtom(aN1))
      tList = vN1 :: tList
    })
    (fN, tList.reverse, scN)
  } 

  def notTopLevelSums(f:Formula,fS:Formula,sc:Int):(Formula,Formula,Int) = f match {
    case FAnd(f1,f2) => {
      val (f1n, fS1, sc1) = notTopLevelSums(f1, fS, sc)
      val (f2n, fS2, sc2) = notTopLevelSums(f2, fS1, sc1)
      (FAnd(f1n, f2n), fS2, sc2)
    }
    case FOr(f1,f2) => {
      val (f1n, fS1, sc1) = notTopLevelSums(f1, fS, sc)
      val (f2n, fS2, sc2) = notTopLevelSums(f2, fS1, sc1)
      (FOr(f1n, f2n), fS2, sc2)
    }
    case FNot(f1)  => {
      val (f1n, fS1, sc1) = notTopLevelSums(f1, fS, sc)
      (FNot(f1n), fS1, sc1)
    }
    case FAtom(AAtomOut(AOSum(lTO, ff, lTI))) => {
      val (f1, l1, scN) = createEqualityFormula(lTO, sc)
      val fN = uniteSums(l1, lTI, ff, fS)
      (f1, fN, scN)
    }
    case FAtom(a)  => (f, fS, sc)
    case FTrue  => (f, fS, sc)
    case FFalse  => (f, fS, sc)
  }
// end


// start: input formula F, output: formula F' which does not contain True and False
// only can contain either pure TRUE or FALSE
  def removeTrueandFalsefromTermIn(t: TermIn): TermIn = t match {
    case TIPlus(t1, t2) => {
      val t1n  = removeTrueandFalsefromTermIn(t1)
      val t2n  = removeTrueandFalsefromTermIn(t2)
      TIPlus(t1n, t2n)
    }
    case TITimes(c, t1)=> {
      val t1n  = removeTrueandFalsefromTermIn(t1)
      TITimes(c, t1n)
    }
    case TIIte(f, t1, t2) => {
      val t1n  = removeTrueandFalsefromTermIn(t1)
      val t2n  = removeTrueandFalsefromTermIn(t2)
      val f1 = removeTrueandFalsefromFormulaIn(f)
      TIIte(f1, t1n, t2n)
    }
    case _ => t
  }

  def removeTrueandFalsefromAtomIn(a: AtomIn): AtomIn = a match {
    case AILeq(t1, t2) => {
      val t1n  = removeTrueandFalsefromTermIn(t1)
      val t2n  = removeTrueandFalsefromTermIn(t2)
      AILeq(t1n, t2n)
    }
    case AIEq(t1,t2) => {
      val t1n  = removeTrueandFalsefromTermIn(t1)
      val t2n  = removeTrueandFalsefromTermIn(t2)
      AIEq(t1n, t2n)
    }
  }

  def removeTrueandFalsefromFormulaIn(f: FormulaIn): FormulaIn =  f match {
    case FIAnd(FIFalse, f2) => FIFalse
    case FIAnd(f1, FIFalse) => FIFalse
    case FIAnd(FITrue, f2) => removeTrueandFalsefromFormulaIn(f2)
    case FIAnd(f1, FITrue) => removeTrueandFalsefromFormulaIn(f1)
    case FIAnd(f1, f2) => {
      val f1n  = removeTrueandFalsefromFormulaIn(f1)
      val f2n  = removeTrueandFalsefromFormulaIn(f2)
      val f3 = if (f1n == FIFalse || f2n == FIFalse) FIFalse else 
        if (f1n == FITrue) f2n else
          if (f2n == FITrue) f1n else FIAnd(f1n, f2n)
      f3
    }
    case FIOr(FITrue, f2) => FITrue
    case FIOr(f1, FITrue) => FITrue
    case FIOr(FIFalse, f2) => removeTrueandFalsefromFormulaIn(f2)
    case FIOr(f1, FIFalse) => removeTrueandFalsefromFormulaIn(f1)
    case FIOr(f1, f2) => {
      val f1n  = removeTrueandFalsefromFormulaIn(f1)
      val f2n  = removeTrueandFalsefromFormulaIn(f2)
      val f3 = if (f1n == FITrue || f2n == FITrue) FITrue else 
        if (f1n == FIFalse) f2n else
          if (f2n == FIFalse) f1n else FIOr(f1n, f2n)
      f3
    }
    case FINot(f1) => {
      val f1n  = removeTrueandFalsefromFormulaIn(f1)
      val f3 = if (f1n == FITrue) FIFalse else 
        if (f1n == FIFalse) FITrue else FINot(f1n)
      f3
    }
    case FIAtom(a) => {
      val a1 = removeTrueandFalsefromAtomIn(a)
      FIAtom(a1)
    }
    case _  => f
  }

  def removeTrueandFalsefromTermOut(t: TermOut): TermOut = t match {
    case TOPlus(t1, t2) => {
      val t1n  = removeTrueandFalsefromTermOut(t1)
      val t2n  = removeTrueandFalsefromTermOut(t2)
      TOPlus(t1n, t2n)
    }
    case TOTimes(c, t1)=> {
      val t1n  = removeTrueandFalsefromTermOut(t1)
      TOTimes(c, t1n)
    }
    case TOIte(f, t1, t2) => {
      val t1n  = removeTrueandFalsefromTermOut(t1)
      val t2n  = removeTrueandFalsefromTermOut(t2)
      val f1 = removeTrueandFalsefromFormulaOut(f)
      TOIte(f1, t1n, t2n)
    }
    case _ => t
  }

  def removeTrueandFalsefromAtomOut(a: AtomOut): AtomOut = a match {
    case AOLeq(t1, t2) => {
      val t1n  = removeTrueandFalsefromTermOut(t1)
      val t2n  = removeTrueandFalsefromTermOut(t2)
      AOLeq(t1n, t2n)
    }
    case AOEq(t1,t2) => {
      val t1n  = removeTrueandFalsefromTermOut(t1)
      val t2n  = removeTrueandFalsefromTermOut(t2)
      AOEq(t1n, t2n)
    }
    case AOSum(l1, f, l2) => {
      val l1n = l1.map(v => removeTrueandFalsefromTermOut(v))
      val l2n = l2.map(v => removeTrueandFalsefromTermIn(v))
      val f1 = removeTrueandFalsefromFormulaIn(f)
      AOSum(l1n, f1, l2n)
    }
  }

  def removeTrueandFalsefromFormulaOut(f: FormulaOut): FormulaOut =  f match {
    case FOAnd(FOFalse, f2) => FOFalse
    case FOAnd(f1, FOFalse) => FOFalse
    case FOAnd(FOTrue, f2) => removeTrueandFalsefromFormulaOut(f2)
    case FOAnd(f1, FOTrue) => removeTrueandFalsefromFormulaOut(f1)
    case FOAnd(f1, f2) => {
      val f1n  = removeTrueandFalsefromFormulaOut(f1)
      val f2n  = removeTrueandFalsefromFormulaOut(f2)
      val f3 = if (f1n == FOFalse || f2n == FOFalse) FOFalse else 
        if (f1n == FOTrue) f2n else
          if (f2n == FOTrue) f1n else FOAnd(f1n, f2n)
      f3
    }
    case FOOr(FOTrue, f2) => FOTrue
    case FOOr(f1, FOTrue) => FOTrue
    case FOOr(FOFalse, f2) => removeTrueandFalsefromFormulaOut(f2)
    case FOOr(f1, FOFalse) => removeTrueandFalsefromFormulaOut(f1)
    case FOOr(f1, f2) => {
      val f1n  = removeTrueandFalsefromFormulaOut(f1)
      val f2n  = removeTrueandFalsefromFormulaOut(f2)
      val f3 = if (f1n == FOTrue || f2n == FOTrue) FOTrue else 
        if (f1n == FOFalse) f2n else
          if (f2n == FOFalse) f1n else FOOr(f1n, f2n)
      f3
    }
    case FONot(f1) => {
      val f1n  = removeTrueandFalsefromFormulaOut(f1)
      val f3 = if (f1n == FOTrue) FOFalse else 
        if (f1n == FOFalse) FOTrue else FONot(f1n)
      f3
    }
    case FOAtom(a) => {
      val a1 = removeTrueandFalsefromAtomOut(a)
      FOAtom(a1)
    }
    case _  => f
  }

  def removeTrueandFalsefromAtom(a: Atom): Atom = a match {
    case AForAllElem(f1) => {
      val f1n = removeTrueandFalsefromFormulaIn(f1)
      AForAllElem(f1n)
    }
    case AAtomOut(a1)  => {
      val a1n = removeTrueandFalsefromAtomOut(a1)
      AAtomOut(a1n)
    }
    case _ => a
  }

  def removeTrueandFalsefromFormulas(f:Formula): Formula = f match {
    case FAnd(FFalse, f2) => FFalse
    case FAnd(f1, FFalse) => FFalse
    case FAnd(FTrue, f2) => removeTrueandFalsefromFormulas(f2)
    case FAnd(f1, FTrue) => removeTrueandFalsefromFormulas(f1)
    case FAnd(f1, f2) => {
      val f1n  = removeTrueandFalsefromFormulas(f1)
      val f2n  = removeTrueandFalsefromFormulas(f2)
      val f3 = if (f1n == FFalse || f2n == FFalse) FFalse else 
        if (f1n == FTrue) f2n else
          if (f2n == FTrue) f1n else FAnd(f1n, f2n)
      f3
    }
    case FOr(FTrue, f2) => FTrue
    case FOr(f1, FTrue) => FTrue
    case FOr(FFalse, f2) => removeTrueandFalsefromFormulas(f2)
    case FOr(f1, FFalse) => removeTrueandFalsefromFormulas(f1)
    case FOr(f1, f2) => {
      val f1n  = removeTrueandFalsefromFormulas(f1)
      val f2n  = removeTrueandFalsefromFormulas(f2)
      val f3 = if (f1n == FTrue || f2n == FTrue) FTrue else 
        if (f1n == FFalse) f2n else
          if (f2n == FFalse) f1n else FOr(f1n, f2n)
      f3
    }
    case FNot(f1) => {
      val f1n  = removeTrueandFalsefromFormulas(f1)
      val f3 = if (f1n == FTrue) FFalse else 
        if (f1n == FFalse) FTrue else FNot(f1n)
      f3
    }
    case FAtom(a) => {
      val a1 = removeTrueandFalsefromAtom(a)
      FAtom(a1)
    }
    case _  => f
  }
// end


// ------------- MAIN -------------

  def main(f:Formula): (Formula,Formula,Formula) = {
    val f0 = removeTrueandFalsefromFormulas(f)
    // formula f0 does not contain true or false but it could be only true or false
    val msetCounter = 0
    var msets: List[(String,Multiset)] = Nil
    val (f1, mc, mcm) = extractMsetsExpr_formula(f0, msetCounter, msets)
    // formula f1 does not contain complex multisets, they are all in mcm
    val toBeChecked = true
    val mlist = flatten_multisetList(mc, mcm, toBeChecked)
    val fAll = createFormulafromMultisetList(mlist)
    // fAll is a formula All e.m1(e) =  ,.. AND ... <- all complex multiset experssions as a formula
    val f2 = redefineMultisetAtoms(f1)  //replace m1 = m2 and m1 SubSET m2 with for all e....
    val intCounter = 0
    var cards: List[(String,String)] = Nil
    val (f3, ic, il) = extractCardExpr_formula(f2, intCounter, cards)
    // f3 = new formula without cardinalities, il = list of the form (intVar, msetVar)
    val fSum = createFormulafromCardinalityList(il)
    // fSum <- atom about all cardinalities that were pulled out of the original formula
    val (f4, fAll1) = topLevelForAll(f3, fAll)
    // all top level forall are united in formula fAll1 and f4 does not contain top-level forall e...
    val f5 = notTopLevelForAll(f4)
    // f5 does not contain any forall e. f(e) expression - they are converted using sums
    val (f6, fSum1) = topLevelSums(f5, fSum)
    // all top level sums are united in formula fSum1 and f6 does not contain top-level sum
    val sumCounter = 0
    val (f7, fSum2, _) = notTopLevelSums(f6, fSum1, sumCounter)
    (f7, fAll1, fSum2)
  } 


}
