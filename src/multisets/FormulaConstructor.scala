package multisets

import scala.collection.mutable.Map
import scala.collection.mutable.Set
import java.util.NoSuchElementException
import multisets.MultisetFormulaPrinter._



object FormulaConstructor {


// start: exists the execution with a message
  def abort(msg: String) {
    println(msg)
    System.exit(-1)
  }

// start: parsing of NoSuchElementException message
  def whichVarIsMissing(s: String): String = {
      val strings = s.split (":");
      strings(1)
  }
// end


// Start: we check for atoms of a type a = b, whether it is about msets or integers
  def checkTypesOfAtom(s: String, m: Map[String, String], a: Atom): Atom = {
    try {
      val af = a match {
        case AEqual(MVariable(m1), MVariable(m2)) => {
          val aN = if (m(m1) == "INT" && m(m2) == "INT") AAtomOut(AOEq(TOVariable(m1), TOVariable(m2)))
          else a
          aN
        }
        case AAtomOut(AOEq(TOVariable(v1), TOVariable(v2)))  => {
          val aN = if (m(v1) == "INT" && m(v2) == "INT") a
          else AEqual(MVariable(v1), MVariable(v2))
          aN
        }
        case _ => a
      }
      af
    } catch {
       case ex: NoSuchElementException => {
         val v = whichVarIsMissing(ex.getMessage)
         abort("Program abort: in the problem " + s + " the variable " + v + " is not declared!")
         AEqual(MEmpty, MEmpty)
       }
    }
  }

  def checkAtomsInFormula(s: String, p: (Map[String, String], Formula)): Formula = p._2 match {
    case FAnd(f1, f2) => {
      val f1N = checkAtomsInFormula(s, (p._1, f1))
      val f2N = checkAtomsInFormula(s, (p._1, f2))
      FAnd(f1N, f2N)
    }
    case FOr(f1, f2) => {
      val f1N = checkAtomsInFormula(s, (p._1, f1))
      val f2N = checkAtomsInFormula(s, (p._1, f2))
      FOr(f1N, f2N)
    }
    case FNot(f1)  => {
      val f1N = checkAtomsInFormula(s, (p._1, f1))
      FNot(f1N)
    }
    case FAtom(a)  => {
      val aN = checkTypesOfAtom(s, p._1, a)
      FAtom(aN)
    }
    case FTrue  => p._2
    case FFalse  => p._2
  }
// end

// start: given a formula we derive two sets of variables: integer variables and set veriables
  def getVariablesfromMultiset(m: Multiset): (Set[String], Set[String]) = m match {
    case MVariable(v) => (Set[String](), Set(v))
    case MEmpty => (Set[String](), Set[String]())
    case MUnion(m1, m2) => {
      val (s1, s2)  = getVariablesfromMultiset(m1)
      val (p1, p2) = getVariablesfromMultiset(m2)
      (s1 ++ p1, s2 ++ p2)
    }
    case MIntersection(m1, m2) => {
      val (s1, s2)  = getVariablesfromMultiset(m1)
      val (p1, p2) = getVariablesfromMultiset(m2)
      (s1 ++ p1, s2 ++ p2)
    }
    case MPlus(m1, m2) => {
      val (s1, s2)  = getVariablesfromMultiset(m1)
      val (p1, p2) = getVariablesfromMultiset(m2)
      (s1 ++ p1, s2 ++ p2)
    }
    case MMinus(m1, m2) => {
      val (s1, s2)  = getVariablesfromMultiset(m1)
      val (p1, p2) = getVariablesfromMultiset(m2)
      (s1 ++ p1, s2 ++ p2)
    }
    case MSetMinus(m1, m2) => {
      val (s1, s2)  = getVariablesfromMultiset(m1)
      val (p1, p2) = getVariablesfromMultiset(m2)
      (s1 ++ p1, s2 ++ p2)
    }
    case MSetOf(m1) => getVariablesfromMultiset(m1)
  }

  def getVariablesfromTermIn(t: TermIn): (Set[String], Set[String]) = t match {
    case TIMultiplicity(v) => (Set[String](), Set(v))
    case TIConstant(c) => (Set[String](), Set[String]())
    case TIPlus(t1, t2) => {
      val (s1, s2)  = getVariablesfromTermIn(t1)
      val (p1, p2) = getVariablesfromTermIn(t2)
      (s1 ++ p1, s2 ++ p2)
    }
    case TITimes(c, t1)=> getVariablesfromTermIn(t1)
    case TIIte(f, t1, t2)=> {
      val (s1, s2)  = getVariablesfromTermIn(t1)
      val (p1, p2) = getVariablesfromTermIn(t2)
      val (st, tt) = (s1 ++ p1, s2 ++ p2)
      val (sf, tf) = getVariablesfromFormulaIn(f)
      (sf ++ st, tf ++ tt)
    }
  }

  def getVariablesfromAtomIn(a: AtomIn): (Set[String], Set[String]) = a match {
    case AILeq(t1, t2) => {
      val (s1, s2)  = getVariablesfromTermIn(t1)
      val (p1, p2) = getVariablesfromTermIn(t2)
      (s1 ++ p1, s2 ++ p2)
    }
    case AIEq(t1,t2) => {
      val (s1, s2)  = getVariablesfromTermIn(t1)
      val (p1, p2) = getVariablesfromTermIn(t2)
      (s1 ++ p1, s2 ++ p2)
    }
  }

  def getVariablesfromFormulaIn(f: FormulaIn): (Set[String], Set[String]) = f match {
    case FIAnd(f1, f2) => {
      val (s1, s2)  = getVariablesfromFormulaIn(f1)
      val (t1, t2) = getVariablesfromFormulaIn(f2)
      (s1 ++ t1, s2 ++ t2)
    }
    case FIOr(f1, f2) => {
      val (s1, s2)  = getVariablesfromFormulaIn(f1)
      val (t1, t2) = getVariablesfromFormulaIn(f2)
      (s1 ++ t1, s2 ++ t2)
    }
    case FINot(f1)  => getVariablesfromFormulaIn(f1)
    case FIAtom(a)  => getVariablesfromAtomIn(a)
    case FITrue  => (Set[String](), Set[String]())
    case FIFalse  => (Set[String](), Set[String]())
  }

  def getVariablesfromTermOut(t: TermOut): (Set[String], Set[String]) = t match {
    case TOConstant(c) => (Set[String](), Set[String]())
    case TOVariable(v) => (Set(v), Set[String]())
    case TOCard(m) => getVariablesfromMultiset(m)
    case TOPlus(t1, t2) => {
      val (s1, s2)  = getVariablesfromTermOut(t1)
      val (p1, p2) = getVariablesfromTermOut(t2)
      (s1 ++ p1, s2 ++ p2)
    }
    case TOTimes(c, t1)=> getVariablesfromTermOut(t1)
    case TOIte(f, t1, t2)=> {
      val (s1, s2)  = getVariablesfromTermOut(t1)
      val (p1, p2) = getVariablesfromTermOut(t2)
      val (st, tt) = (s1 ++ p1, s2 ++ p2)
      val (sf, tf) = getVariablesfromFormulaOut(f)
      (sf ++ st, tf ++ tt)
    }
  }

  def getVariablesfromAtomOut(a: AtomOut): (Set[String], Set[String]) = a match {
    case AOLeq(t1, t2) => {
      val (s1, s2)  = getVariablesfromTermOut(t1)
      val (p1, p2) = getVariablesfromTermOut(t2)
      (s1 ++ p1, s2 ++ p2)
    }
    case AOEq(t1,t2) => {
      val (s1, s2)  = getVariablesfromTermOut(t1)
      val (p1, p2) = getVariablesfromTermOut(t2)
      (s1 ++ p1, s2 ++ p2)
    }
    case AOSum(l1, f, l2) => {
      var s = Set[String]()
      var t = Set[String]()
      l1.foreach(v => {
        val (st, tt) = getVariablesfromTermOut(v)
        s = s ++ st
        t = t ++ tt
      })
      l2.foreach(v => {
        val (st, tt) = getVariablesfromTermIn(v)
        s = s ++ st
        t = t ++ tt
      })
      val (sf, tf) = getVariablesfromFormulaIn(f)
      (s ++ sf, t ++ tf)
    }
  }

  def getVariablesfromFormulaOut(f: FormulaOut): (Set[String], Set[String]) = f match {
    case FOAnd(f1, f2) => {
      val (s1, s2)  = getVariablesfromFormulaOut(f1)
      val (t1, t2) = getVariablesfromFormulaOut(f2)
      (s1 ++ t1, s2 ++ t2)
    }
    case FOOr(f1, f2) => {
      val (s1, s2)  = getVariablesfromFormulaOut(f1)
      val (t1, t2) = getVariablesfromFormulaOut(f2)
      (s1 ++ t1, s2 ++ t2)
    }
    case FONot(f1)  => getVariablesfromFormulaOut(f1)
    case FOAtom(a)  => getVariablesfromAtomOut(a)
    case FOTrue  => (Set[String](), Set[String]())
    case FOFalse  => (Set[String](), Set[String]())
  }

  def getVariablesfromAtom(a: Atom): (Set[String], Set[String]) = a match {
    case AEqual(m1, m2) => {
      val (s1, s2)  = getVariablesfromMultiset(m1)
      val (t1, t2) = getVariablesfromMultiset(m2)
      (s1 ++ t1, s2 ++ t2)
    }
    case ASubset(m1,m2) => {
      val (s1, s2)  = getVariablesfromMultiset(m1)
      val (t1, t2) = getVariablesfromMultiset(m2)
      (s1 ++ t1, s2 ++ t2)
    }
    case AForAllElem(f1) => getVariablesfromFormulaIn(f1)
    case AAtomOut(a1)  => getVariablesfromAtomOut(a1)
  }

  def getVariablesfromFormula(f: Formula): (Set[String], Set[String]) = f match {
    case FAnd(f1, f2) => {
      val (s1, s2)  = getVariablesfromFormula(f1)
      val (t1, t2) = getVariablesfromFormula(f2)
      (s1 ++ t1, s2 ++ t2)
    }
    case FOr(f1, f2) => {
      val (s1, s2)  = getVariablesfromFormula(f1)
      val (t1, t2) = getVariablesfromFormula(f2)
      (s1 ++ t1, s2 ++ t2)
    }
    case FNot(f1)  => getVariablesfromFormula(f1)
    case FAtom(a)  => getVariablesfromAtom(a)
    case FTrue  => (Set[String](), Set[String]())
    case FFalse  => (Set[String](), Set[String]())
  }
// end


// start: checking that all types are correct
  def checkTypesOfIntVariables(name: String, m: Map[String, String], ints: List[String]): Unit = {
    try {
      ints.foreach(v => if (m(v) != "INT") 
        abort("Program abort: in the problem " + name + " the INT variable " + v + " is declared as" + m(v) +  "!")
      )
    } catch {
       case ex: NoSuchElementException => {
         val v = whichVarIsMissing(ex.getMessage)
         abort("Program abort: in the problem " + name + " the variable " + v + " is not declared!")
         AEqual(MEmpty, MEmpty)
       }
    }
  }

  def checkTypesOfMSetVariables(name: String, m: Map[String, String], msets: List[String]): Unit = {
    try {
      msets.foreach(v => if (m(v) == "INT") 
        abort("Program abort: in the problem " + name + " the collection variable " + v + " is declared as INT!")
      )
    } catch {
       case ex: NoSuchElementException => {
         val v = whichVarIsMissing(ex.getMessage)
         abort("Program abort: in the problem " + name + " the variable " + v + " is not declared!")
         AEqual(MEmpty, MEmpty)
       }
    }
  } 

  def simpleTypeChecking(name: String, m: Map[String, String], ints: List[String], msets: List[String]): Unit = {
    checkTypesOfIntVariables(name, m, ints)
    checkTypesOfMSetVariables(name, m, msets)
  }
// end


// start: here we construct formulas describing that S is a SET or e is an ELEM
  def createConstraintAboutOneVar(t: String, v:String): Formula = {
    val f = if (t == "SET") {
      val f1in = FIAtom(AIEq(TIMultiplicity(v), TIConstant(0)))
      val f2in = FIAtom(AIEq(TIMultiplicity(v), TIConstant(1)))
      FAtom(AForAllElem(FIOr(f1in, f2in)))
    } else FAtom(AAtomOut(AOEq(TOCard(MVariable(v)), TOConstant(1))))
    f
  }

  def getAdditionalConstraints(m: Map[String, String], l: List[String]): Formula =  {
    val ln = l.filter(v => m(v) != "MSET")
    val f = if (ln.isEmpty) FTrue else {
      var ft = createConstraintAboutOneVar(m(ln.head), ln.head)
      val lnt = ln.tail
      lnt.foreach(v =>  {
        val fn = createConstraintAboutOneVar(m(v), v)
        ft = FAnd(ft, fn)
      })
      ft
    }
    f
  }
// end


// start:  translation to NNF
  def nnfTermIn(t: TermIn): TermIn = t match {
    case TIPlus(t1, t2) => {
      val t1n  = nnfTermIn(t1)
      val t2n  = nnfTermIn(t2)
      TIPlus(t1n, t2n)
    }
    case TITimes(c, t1)=> {
      val t1n  = nnfTermIn(t1)
      TITimes(c, t1n)
    }
    case TIIte(f, t1, t2) => {
      val t1n  = nnfTermIn(t1)
      val t2n  = nnfTermIn(t2)
      val f1 = nnfFormulaIn(f)
      TIIte(f1, t1n, t2n)
    }
    case _ => t
  }

  def nnfAtomIn(a: AtomIn): AtomIn = a match {
    case AILeq(t1, t2) => {
      val t1n  = nnfTermIn(t1)
      val t2n  = nnfTermIn(t2)
      AILeq(t1n, t2n)
    }
    case AIEq(t1,t2) => {
      val t1n  = nnfTermIn(t1)
      val t2n  = nnfTermIn(t2)
      AIEq(t1n, t2n)
    }
  }

  def nnfFormulaIn(f: FormulaIn): FormulaIn =  f match {
    case FIAnd(f1, f2) => {
      val f1n  = nnfFormulaIn(f1)
      val f2n  = nnfFormulaIn(f2)
      FIAnd(f1n, f2n)
    }
    case FIOr(f1, f2) => {
      val f1n  = nnfFormulaIn(f1)
      val f2n  = nnfFormulaIn(f2)
      FIOr(f1n, f2n)
    }
    case FINot(FIAnd(f1, f2)) => {
      val f1n  = nnfFormulaIn(FINot(f1))
      val f2n  = nnfFormulaIn(FINot(f2))
      FIOr(f1n, f2n)
    }
    case FINot(FIOr(f1, f2)) => {
      val f1n  = nnfFormulaIn(FINot(f1))
      val f2n  = nnfFormulaIn(FINot(f2))
      FIAnd(f1n, f2n)
    }
    case FINot(FINot(f1))  => nnfFormulaIn(f1)
    case FINot(FIAtom(a)) => {
      val a1 = nnfAtomIn(a)
      FINot(FIAtom(a1))
    }
    case FINot(FITrue)  => FIFalse 
    case FINot(FIFalse)  => FITrue
    case FIAtom(a) => {
      val a1 = nnfAtomIn(a)
      FIAtom(a1)
    }
    case _  => f
  }


  def nnfTermOut(t: TermOut): TermOut = t match {
    case TOPlus(t1, t2) => {
      val t1n  = nnfTermOut(t1)
      val t2n  = nnfTermOut(t2)
      TOPlus(t1n, t2n)
    }
    case TOTimes(c, t1)=> {
      val t1n  = nnfTermOut(t1)
       TOTimes(c, t1n)
    }
    case TOIte(f, t1, t2) => {
      val t1n  = nnfTermOut(t1)
      val t2n  = nnfTermOut(t2)
      val f1 = nnfFormulaOut(f)
      TOIte(f1, t1n, t2n)
    }
    case _ => t
  }

  def nnfAtomOut(a: AtomOut): AtomOut = a match {
    case AOLeq(t1, t2) => {
      val t1n  = nnfTermOut(t1)
      val t2n  = nnfTermOut(t2)
      AOLeq(t1n, t2n)
    }
    case AOEq(t1,t2) => {
      val t1n  = nnfTermOut(t1)
      val t2n  = nnfTermOut(t2)
      AOEq(t1n, t2n)
    }
    case AOSum(l1, f, l2) => {
      val l1n = l1.map(v => nnfTermOut(v))
      val l2n = l2.map(v => nnfTermIn(v))
      val f1 = nnfFormulaIn(f)
      AOSum(l1n, f1, l2n)
    }
  }

  def nnfFormulaOut(f: FormulaOut): FormulaOut =  f match {
    case FOAnd(f1, f2) => {
      val f1n  = nnfFormulaOut(f1)
      val f2n  = nnfFormulaOut(f2)
      FOAnd(f1n, f2n)
    }
    case FOOr(f1, f2) => {
      val f1n  = nnfFormulaOut(f1)
      val f2n  = nnfFormulaOut(f2)
      FOOr(f1n, f2n)
    }
    case FONot(FOAnd(f1, f2)) => {
      val f1n  = nnfFormulaOut(FONot(f1))
      val f2n  = nnfFormulaOut(FONot(f2))
      FOOr(f1n, f2n)
    }
    case FONot(FOOr(f1, f2)) => {
      val f1n  = nnfFormulaOut(FONot(f1))
      val f2n  = nnfFormulaOut(FONot(f2))
      FOAnd(f1n, f2n)
    }
    case FONot(FONot(f1))  => nnfFormulaOut(f1)
    case FONot(FOAtom(a)) => {
      val a1 = nnfAtomOut(a)
      FONot(FOAtom(a1))
    }
    case FONot(FOTrue)  => FOFalse 
    case FONot(FOFalse)  => FOTrue
    case FOAtom(a) => {
      val a1 = nnfAtomOut(a)
      FOAtom(a1)
    }
    case _  => f
  }

  def nnfAtom(a: Atom): Atom = a match {
    case AForAllElem(f1) => {
      val f1n = nnfFormulaIn(f1)
      AForAllElem(f1n)
    }
    case AAtomOut(a1)  => {
      val a1n = nnfAtomOut(a1)
      AAtomOut(a1n)
    }
    case _ => a
  }

  def nnf(f: Formula): Formula = f match {
    case FAnd(f1, f2) => {
      val f1n  = nnf(f1)
      val f2n  = nnf(f2)
      FAnd(f1n, f2n)
    }
    case FOr(f1, f2) => {
      val f1n  = nnf(f1)
      val f2n  = nnf(f2)
      FOr(f1n, f2n)
    }
    case FNot(FAnd(f1, f2)) => {
      val f1n  = nnf(FNot(f1))
      val f2n  = nnf(FNot(f2))
      FOr(f1n, f2n)
    }
    case FNot(FOr(f1, f2)) => {
      val f1n  = nnf(FNot(f1))
      val f2n  = nnf(FNot(f2))
      FAnd(f1n, f2n)
    }
    case FNot(FNot(f1))  => nnf(f1)
    case FNot(FAtom(a)) => {
      val a1 = nnfAtom(a)
      FNot(FAtom(a1))
    }
    case FNot(FTrue)  => FFalse 
    case FNot(FFalse)  => FTrue
    case FAtom(a) => {
      val a1 = nnfAtom(a)
      FAtom(a1)
    }
    case _  => f
  }
// end


// start: input problem, output: (name, created-formula, negated-created-formula, constraints)
// all output formulas are in NNF
  def processOneProblem(p: (String, (Map[String, String], Formula))): (String, (Formula, Formula, Formula)) = {
    val mf = p._2
    val f1 = checkAtomsInFormula(p._1, mf)
    val f1f = nnf(f1)
    val (sInt, sMsets) = getVariablesfromFormula(f1)
    val lInt = sInt.toList
    val lMsets = sMsets.toList
    val m  = mf._1
    simpleTypeChecking(p._1, m, lInt, lMsets)
    val fc = getAdditionalConstraints(m, lMsets)
    val fcf = nnf(fc)
    val fN = nnf(FNot(f1))
    (p._1,  (f1f, fN, fcf))
  }
// end



//------------------------------------------------

  def main(problemList: List[(String, (Map[String, String], Formula))]) : List[(String, (Formula, Formula, Formula))] = {
    val formulaList = problemList.map(p => processOneProblem(p))
    formulaList
  }
}

