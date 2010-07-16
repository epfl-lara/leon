package mapaFun


object MAPAFunFormulaPrinter {

  def print_MAPAFunInt(i: MAPAFunInt): Unit = i match {
    case MFIntVar(v) => Console.print(v)
    case MFIntConst(c) => Console.print(c)
    case MFIPlus(i1, i2) => {
      print_MAPAFunInt(i1)
      Console.print(" + ")
      print_MAPAFunInt(i2)
    }
    case MFITimes(c, i1) => {
      Console.print(c + "*")
      print_MAPAFunInt(i1)
    }
    case MFSCard(s) => {
      Console.print("| ")
      print_MAPAFunSet(s)
      print(" |")
    }
    case MFMCard(m) => {
      Console.print("| ")
      print_MAPAFunMultiset(m)
      print(" |")
    }
  }

  def print_MAPAFunMultiset(m: MAPAFunMultiset):Unit = m match {
    case MFMSetVar(v) => Console.print(v)
    case MFEmptyMSet => Console.print("EMPTY MULTISET")
    case MFMUnion(m1, m2) => {
      print_MAPAFunMultiset(m1)
      Console.print(" UNION ")
      print_MAPAFunMultiset(m2)
    }
    case MFMIntersec(m1, m2) => {
      print_MAPAFunMultiset(m1)
      Console.print(" INTERSEC ")
      print_MAPAFunMultiset(m2)
    }
    case MFMPlus(m1, m2) => {
      print_MAPAFunMultiset(m1)
      Console.print(" PLUS ")
      print_MAPAFunMultiset(m2)
    }
    case MFMMinus(m1, m2) => {
      print_MAPAFunMultiset(m1)
      Console.print(" MINUS ")
      print_MAPAFunMultiset(m2)
    }
    case MFSetMinus(m1, m2) => {
      print_MAPAFunMultiset(m1)
      Console.print(" SET MINUS ")
      print_MAPAFunMultiset(m2)
    }
    case MFSSetOf(m1) => {
      Console.print(" SETOf ( ")
      print_MAPAFunMultiset(m1)
      print(" )")
    }
    case MFFunction(f, s) => {
      Console.print(f + "[ ")
      print_MAPAFunSet(s)
      print(" ]")
    }
  }

  def print_MAPAFunSet(s: MAPAFunSet):Unit = s match {
    case MFSetVar(v) => Console.print(v)
    case MFEmptySet => Console.print("EMPTY SET")
    case MFUnivSet => Console.print("UNIVERSAL SET")
    case MFSUnion(s1, s2) => {
      print_MAPAFunSet(s1)
      Console.print(" UNION ")
      print_MAPAFunSet(s2)
    }
    case MFSIntersec(s1, s2) => {
      print_MAPAFunSet(s1)
      Console.print(" INTERSEC ")
      print_MAPAFunSet(s2)
    }
    case MFSCompl(s1) => {
      Console.print("( ")
      print_MAPAFunSet(s1)
      print(" )^c ")
    }
  }


  def print_MAPAFunAtom(a: MAPAFunAtom):Unit = a match {
    case MFSetEqual(s1, s2) => {
      print_MAPAFunSet(s1)
      Console.print(" = ")
      print_MAPAFunSet(s2)
    }
    case MFSetSubset(s1, s2) => {
      print_MAPAFunSet(s1)
      Console.print(" SUBSET ")
      print_MAPAFunSet(s2)
    }
    case MFMSetEqual(m1, m2) => {
      print_MAPAFunMultiset(m1)
      Console.print(" = ")
      print_MAPAFunMultiset(m2)
    }
    case MFMSetSubset(m1, m2) => {
      print_MAPAFunMultiset(m1)
      Console.print(" SUBSET ")
      print_MAPAFunMultiset(m2)
    }
    case MFIntEqual(i1, i2) => {
      print_MAPAFunInt(i1)
      Console.print(" = ")
      print_MAPAFunInt(i2)
    }
    case MFIntLessEqual(i1, i2) => {
      print_MAPAFunInt(i1)
      Console.print(" =< ")
      print_MAPAFunInt(i2)
    }
    case MFIntDivides(c, i) => {
      Console.print(c + " * ")
      print_MAPAFunInt(i)
    }
  }


  def print_MAPAFunFormula(f: MAPAFunFormula):Unit = f match {
    case MFAnd(f1, f2) => {
      Console.print(" ( ")
      print_MAPAFunFormula(f1)
      print(" ) AND ( ")
      print_MAPAFunFormula(f2)
      print(" ) ")
    }
    case MFOr(f1, f2) => {
      Console.print(" ( ")
      print_MAPAFunFormula(f1)
      print(" ) OR ( ")
      print_MAPAFunFormula(f2)
      print(" ) ")
    }
    case MFNot(f1)  => {
      Console.print(" NOT ( ")
      print_MAPAFunFormula(f1)
      print(" ) ")
    }
    case MFAtom(a)  => print_MAPAFunAtom(a)
  }

}