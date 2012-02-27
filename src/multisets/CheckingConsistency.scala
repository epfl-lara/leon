package multisets
import scala.collection.mutable.Map
import scala.collection.mutable.Set
//import java.io._

import z3.scala._

object CheckingConsistency {




/*



  def createVariableString(va:Array[String]):String = {
   var s = ""
   va.foreach(v => s = s + "(" + v + " Int) ")
   s
  }


  def createSMTRepresentationOfTerm(t:TermQFPA):String = t match {
    case TVariable(v) => v
    case TConstant(c) =>  c.toString
    case TPlus(t1, t2) => {
      val s1 = createSMTRepresentationOfTerm(t1)
      val s2 = createSMTRepresentationOfTerm(t2)
      "(+ " + s1 + " " + s2 + ")"
    }
    case TTimes(c, t1) => {
      val s1 = createSMTRepresentationOfTerm(t1)
      "(* " + c.toString + " " + s1 + ")"
    }
    case x@_ => error("Impossible case :" + x)
  }

  def createSMTRepresentationOfAtom(a:AtomQFPA):String = a match {
    case ALeq(t1, t2) => {
      val s1 = createSMTRepresentationOfTerm(t1)
      val s2 = createSMTRepresentationOfTerm(t2)
      "(<= " + s1 + " " + s2 + ")"
    }
    case AEq(t1, t2) => {
      val s1 = createSMTRepresentationOfTerm(t1)
      val s2 = createSMTRepresentationOfTerm(t2)
      "(= " + s1 + " " + s2 + ")"
    }
  }

  def createSMTRepresentationOfFormula(f:QFPAFormula):String = {
    val s = f match {
      case QFPAAnd(f1, f2) => {
        val s1 = createSMTRepresentationOfFormula(f1)
        val s2 = createSMTRepresentationOfFormula(f2)
        "and " + s1 + " " + s2
      }
      case QFPAOr(f1, f2) => {
        val s1 = createSMTRepresentationOfFormula(f1)
        val s2 = createSMTRepresentationOfFormula(f2)
        "or " + s1 + " " + s2
      }
      case QFPANot(f1) => {
        val s1 = createSMTRepresentationOfFormula(f1)
        "not " + s1
      }
      case QFPAAtom(a) => createSMTRepresentationOfAtom(a)
      case _ => " "
    }
    "( " + s + " )"
  }


  def callZ3toDetermineConsistency(c:List[QFPAFormula]):String = {
    val smtfile = File.createTempFile("iteremove", ".smt");
    val smtfileName = smtfile.getAbsolutePath

    val vars = getAllVariablesFromListofFormulas(c)
    val s1 = createVariableString(vars)

    val out = new BufferedWriter(new FileWriter(smtfile))
    out.write("(benchmark example")
    out.newLine()
    out.write(":logic QF_LIA")
    out.newLine()
    out.write(":extrafuns (")
    out.write(s1)
    out.write(")")
    out.newLine()
    out.write(":formula (and")
    out.newLine()
    vars.foreach (v => {
      out.write("(<=  0 " + v + " )" )
      out.newLine()
    })
    c.foreach(g => {
      val sg = createSMTRepresentationOfFormula(g)
      out.write(sg)
      out.newLine()
    })
    out.write(")")
    out.newLine()
    out.write(")")
    out.newLine()
    out.close

    val cmd =  Array("z3.exe.linux", smtfileName)
    val p: Process = Runtime.getRuntime.exec(cmd)
    val input: BufferedReader = new BufferedReader(new InputStreamReader(p.getInputStream()))
    val line: String = input.readLine
    p.waitFor
    input.close

    smtfile.deleteOnExit
    line
  }


  def checkConsistencyofOneFormula(f:QFPAFormula): List[String] = {
    val smtfile = File.createTempFile("finalFormula", ".smt");
    val smtfileName = smtfile.getAbsolutePath

    val vars = getAllVariablesFromOneFormula(f)
    val s1 = createVariableString(vars)

    val out = new BufferedWriter(new FileWriter(smtfile))
    out.write("(benchmark example")
    out.newLine()
    out.write(":logic QF_LIA")
    out.newLine()
    out.write(":extrafuns (")
    out.write(s1)
    out.write(")")
    out.newLine()
    out.write(":formula (and")
    out.newLine()
    vars.foreach (v => {
      out.write("(<=  0 " + v + " )" )
      out.newLine()
    })
    val sg = createSMTRepresentationOfFormula(f)
    out.write(sg)
    out.newLine()
    out.write(")")
    out.newLine()
    out.write(")")
    out.newLine()
    out.close

    val cmd =  Array("z3", "-m", smtfileName)
    val p: Process = Runtime.getRuntime.exec(cmd)
    val input: BufferedReader = new BufferedReader(new InputStreamReader(p.getInputStream()))
    var line = input.readLine()
    var l: List[String] = Nil
    while (line != null) {
      l = line :: l
      line = input.readLine()
    }
    p.waitFor
    input.close

    smtfile.deleteOnExit
    l
  }  */


// start: getting out all variables

  def getAllVariablesAndConstsFromTerm(t:TermQFPA):(Set[String], Set[Int]) = t match {
    case TVariable(v) => (Set(v), Set[Int]())
    case TConstant(c) =>  (Set[String](), Set(c))
    case TPlus(t1, t2) => {
      val p1 = getAllVariablesAndConstsFromTerm(t1)
      val p2 = getAllVariablesAndConstsFromTerm(t2)
      (p1._1 ++ p2._1, p1._2 ++ p2._2)
    }
    case TTimes(c, t1) => {
      val p1 = getAllVariablesAndConstsFromTerm(t1)
      (p1._1, p1._2 ++ Set(c))
    }
    case TIte(f, t1, t2) => {
      val p0 = getAllVariablesAndConstsFromFormula(f)
      val p1 = getAllVariablesAndConstsFromTerm(t1)
      val p2 = getAllVariablesAndConstsFromTerm(t2)
      (p0._1 ++ p1._1 ++ p2._1, p0._2 ++ p1._2 ++ p2._2)
    }
  }

  def getAllVariablesAndConstsFromAtom(a:AtomQFPA):(Set[String], Set[Int]) = a match {
    case ALeq(t1, t2) => {
      val p1 = getAllVariablesAndConstsFromTerm(t1)
      val p2 = getAllVariablesAndConstsFromTerm(t2)
      (p1._1 ++ p2._1, p1._2 ++ p2._2)
    }
    case AEq(t1, t2) => {
      val p1 = getAllVariablesAndConstsFromTerm(t1)
      val p2 = getAllVariablesAndConstsFromTerm(t2)
      (p1._1 ++ p2._1, p1._2 ++ p2._2)
    }
  }

  def getAllVariablesAndConstsFromFormula(f:QFPAFormula):(Set[String], Set[Int]) = f match {
    case QFPAAnd(f1, f2) => {
      val p1 = getAllVariablesAndConstsFromFormula(f1)
      val p2 = getAllVariablesAndConstsFromFormula(f2)
      (p1._1 ++ p2._1, p1._2 ++ p2._2)
    }
    case QFPAOr(f1, f2) => {
      val p1 = getAllVariablesAndConstsFromFormula(f1)
      val p2 = getAllVariablesAndConstsFromFormula(f2)
      (p1._1 ++ p2._1, p1._2 ++ p2._2)
    }
    case QFPANot(f1) => getAllVariablesAndConstsFromFormula(f1)
    case QFPAAtom(a) => getAllVariablesAndConstsFromAtom(a)
    case QFPAFalse => (Set[String](), Set[Int]())
    case QFPATrue => (Set[String](), Set[Int]())
  }


  def getAllVariablesAndConstsFromListofFormulas(c:List[QFPAFormula]): (Set[String], Set[Int]) = {
    var p = (Set[String](), Set[Int]())
    c.foreach(g => {
      val p1 = getAllVariablesAndConstsFromFormula(g)
      p = (p._1 ++ p1._1, p._2 ++ p1._2) 
    })
    p
  }

// end



  def mkASTTerm(t:TermQFPA, s: Z3Sort, z3: Z3Context): (Z3AST, Z3Sort, Z3Context) = t match {
    case TConstant(c) => (z3.mkInt(c, s), s, z3)
    case TVariable(v) => (z3.mkConst(z3.mkStringSymbol(v), s), s, z3)
    case TPlus(t1, t2) =>  {
      val t1N = mkASTTerm(t1, s, z3)._1
      val t2N = mkASTTerm(t2, s, z3)._1
      (z3.mkAdd(t1N, t2N), s, z3)
    }
    case TTimes(c, t1)=> {
      val cN = z3.mkInt(c, s)
      val t1N = mkASTTerm(t1, s, z3)._1
      (z3.mkMul(cN, t1N), s, z3)
    }
    case TIte(f, t1, t2)=> {
      val fN = mkAST(f, s, z3)._1
      val t1N = mkASTTerm(t1, s, z3)._1
      val t2N = mkASTTerm(t2, s, z3)._1
      (z3.mkITE(fN, t1N, t2N), s, z3)
    }
  }

  def mkASTAtom(a:AtomQFPA, s: Z3Sort, z3: Z3Context): (Z3AST, Z3Sort, Z3Context) = a match {
    case ALeq(t1,t2) => {
      val t1N = mkASTTerm(t1, s, z3)._1
      val t2N = mkASTTerm(t2, s, z3)._1
      (z3.mkLE(t1N, t2N), s, z3)
    }
    case AEq(t1,t2) => {
      val t1N = mkASTTerm(t1, s, z3)._1
      val t2N = mkASTTerm(t2, s, z3)._1
      (z3.mkEq(t1N, t2N), s, z3)
    }
  }

  def mkAST(f: QFPAFormula, s: Z3Sort, z3: Z3Context): (Z3AST, Z3Sort, Z3Context) = f match {
    case QFPAAnd(f1,f2) => {
      val f1N = mkAST(f1, s, z3)._1
      val f2N = mkAST(f2, s, z3)._1
      (z3.mkAnd(f1N, f2N), s, z3)
    }
    case QFPAOr(f1,f2) => {
      val f1N = mkAST(f1, s, z3)._1
      val f2N = mkAST(f2, s, z3)._1
      (z3.mkOr(f1N, f2N), s, z3)
    }
    case QFPANot(f1)  => (z3.mkNot(mkAST(f1, s, z3)._1), s, z3)
    case QFPAAtom(a)  => mkASTAtom(a, s, z3)
    case QFPAFalse => (z3.mkFalse, s, z3)
    case QFPATrue  => (z3.mkTrue, s, z3)
  }


  def callZ3NewWaytoDetermineConsistency(c:List[QFPAFormula]): Boolean = {
    val z3 = new Z3Context((new Z3Config).setParamValue("MODEL", "false"))
    val i = z3.mkIntSort

    val z3formulasPairs = c.map(f => mkAST(f, i, z3))
    val z3formulas = z3formulasPairs.map(f => f._1)
    z3formulas.foreach(f => z3.assertCnstr(f))

    val b = z3.check() match {
      case Some(x) => x
      case None => error("There was an error with Z3.")
    }
    z3.delete
    b
  }


/////////


  def callZ3NewWaytoCheckConsistencyofOneFormula(f:QFPAFormula):(Boolean, Map[String, Int]) = {
    val z3 = new Z3Context((new Z3Config).setParamValue("MODEL", "true"))
    val i = z3.mkIntSort

    val vars = getAllVariablesAndConstsFromFormula(f)._1
    val varMap = Map.empty[String,Z3AST]

    vars.foreach(v => {
      if(!varMap.keySet.contains(v)) {
        val ast = z3.mkConst(z3.mkStringSymbol(v), i)
        varMap(v) = ast
        }
    })

    val z3formulaTuple = mkAST(f, i, z3)
    val z3formula = z3formulaTuple._1
    z3.assertCnstr(z3formula)

    val (res, model) = z3.checkAndGetModel()

    val out = res match {
      case Some(false) => (false, Map.empty[String,Int]) 
      case Some(true) => (true, Map.empty[String,Int] ++ varMap.map(p => (p._1, model.evalAs[Int](p._2).get)))
      case None => error("There was an error with Z3.")
    }
    out
  }




//------------------------------------------
// old names keep consistency with old calls
//------------------------------------------


// calls Z3 on list of formulas and returns "sat" or "unsat"
  def callZ3toDetermineConsistency(c:List[QFPAFormula]):String = {
     val b = callZ3NewWaytoDetermineConsistency(c)
     val s = if (b == true) "sat" else "unsat"
     s
  }


// calls z3 on One formula and return a model and "sat" or "unsat"
  def checkConsistencyofOneFormula(f:QFPAFormula): (String, Map[String, Int]) = {
    val p = callZ3NewWaytoCheckConsistencyofOneFormula(f)
    val res = if (p._1 == true) ("sat", p._2) else ("unsat", p._2)
    res
  }

}
