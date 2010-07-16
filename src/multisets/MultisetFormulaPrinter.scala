package multisets

object MultisetFormulaPrinter {
 
  def print_multiset(m:Multiset):Unit = m match {
    case MVariable(v) => Console.print(v)
    case MEmpty => Console.print("EMPTY")
    case MUnion(m1, m2) => {
      print_multiset(m1)
      Console.print(" UNION ")
      print_multiset(m2)
    }
    case MIntersection(m1, m2) => {
      print_multiset(m1)
      Console.print(" INTERSECT ")
      print_multiset(m2)
    }
    case MPlus(m1, m2) => {
      print_multiset(m1)
      Console.print(" PLUS ")
      print_multiset(m2)
    }
    case MMinus(m1, m2) => {
      print_multiset(m1)
      Console.print(" MINUS ")
      print_multiset(m2)
    }
    case MSetMinus(m1, m2) => {
      print_multiset(m1)
      Console.print(" SetMINUS ")
      print_multiset(m2)
    }
    case MSetOf(m1) => {
      Console.print(" SetOf( ")
      print_multiset(m1)
      print(" )")
    }
  }

  def print_termIn(t:TermIn):Unit = t match {
    case TIMultiplicity(v) => Console.print(v + "(e)")
    case TIConstant(c) => Console.print(c)
    case TIPlus(t1, t2) => {
      print_termIn(t1)
      Console.print(" + ")
      print_termIn(t2)
    }
    case TITimes(c, t1)=> {
      Console.print(c + "*")
      print_termIn(t1)
    }
    case TIIte(f, t1, t2)=> {
      Console.print("ITE(")
      print_formulaIn(f)
      print("; ")
      print_termIn(t1)
      print(", ")
      print_termIn(t2)
      print(")")
    }
  }


  def print_atomIn(a:AtomIn):Unit = a match {
    case AILeq(t1,t2) => {
      print_termIn(t1)
      Console.print(" =< ")
      print_termIn(t2)
    }
    case AIEq(t1,t2) => {
      print_termIn(t1)
      Console.print(" = ")
      print_termIn(t2)
    }
  }

  def print_formulaIn(f:FormulaIn):Unit = f match {
    case FIAnd(f1,f2) => {
      Console.print(" ( ")
      print_formulaIn(f1)
      print(" ) AND ( ")
      print_formulaIn(f2)
      print(" ) ")
    }
    case FIOr(f1,f2) => {
      Console.print(" ( ")
      print_formulaIn(f1)
      print(" ) OR ( ")
      print_formulaIn(f2)
      print(" ) ")
    }
    case FINot(f1)  => {
      Console.print(" NOT ( ")
      print_formulaIn(f1)
      print(" ) ")
    }
    case FIAtom(a) => print_atomIn(a)
    case FITrue => Console.print(" TRUE ")
    case FIFalse => Console.print(" FALSE ")
  }


 
  def print_termOut(t:TermOut):Unit = t match {
    case TOConstant(c) => Console.print(c)
    case TOVariable(v) => Console.print(v)
    case TOCard(m) => {
      Console.print("| ")
      print_multiset(m)
      Console.print("| ")
    }
    case TOPlus(t1, t2) => {
      print_termOut(t1)
      Console.print(" + ")
      print_termOut(t2)
    }
    case TOTimes(c, t1)=> {
      Console.print(c + "*")
      print_termOut(t1)
    }
    case TOIte(f, t1, t2)=> {
      Console.print("ITE(")
      print_formulaOut(f)
      print("; ")
      print_termOut(t1)
      print(", ")
      print_termOut(t2)
      print(")")
    }
  }

  def print_atomOut(a:AtomOut):Unit = a match {
    case AOLeq(t1,t2) => {
      print_termOut(t1)
      Console.print(" =< ")
      print_termOut(t2)
    }
    case AOEq(t1,t2) => {
      print_termOut(t1)
      Console.print(" = ")
      print_termOut(t2)
    }
    case AOSum(l1, f, l2) => {
      Console.print(" ( ")
      l1.foreach(x => {
        print_termOut(x)
        print(", ")
      })
      print(") = SUM {e in E, ")
      print_formulaIn(f)
      print("} (")
      l2.foreach(x => {
        print_termIn(x)
        print(", ")
      })
      print(")")
    }
  }


  def print_formulaOut(f:FormulaOut):Unit = f match {
    case FOAnd(f1,f2) => {
      Console.print(" ( ")
      print_formulaOut(f1)
      print(" ) AND ( ")
      print_formulaOut(f2)
      print(" ) ")
    }
    case FOOr(f1,f2) => {
      Console.print(" ( ")
      print_formulaOut(f1)
      print(" ) OR ( ")
      print_formulaOut(f2)
      print(" ) ")
    }
    case FONot(f1)  => {
      Console.print(" NOT ( ")
      print_formulaOut(f1)
      print(" ) ")
    }
    case FOAtom(a)  => print_atomOut(a)
    case FOTrue => Console.print(" TRUE ")
    case FOFalse => Console.print(" FALSE ")
  }

  def print_atom(a:Atom):Unit = a match {
    case AEqual(m1,m2) => {
      print_multiset(m1)
      Console.print(" = ")
      print_multiset(m2)
    }
    case ASubset(m1,m2) => {
      print_multiset(m1)
      Console.print(" SUBSET ")
      print_multiset(m2)
    }
    case AForAllElem(f) => {
      Console.print(" FOR ALL e IN E. ( ")
      print_formulaIn(f)
      print(" ) ")
    }
    case AAtomOut(a1)  => print_atomOut(a1)
  }

  def print_multisetFormula(f:Formula):Unit = f match {
    case FAnd(f1,f2) => {
      Console.print(" ( ")
      print_multisetFormula(f1)
      print(" ) AND ( ")
      print_multisetFormula(f2)
      print(" ) ")
    }
    case FOr(f1,f2) => {
      Console.print(" ( ")
      print_multisetFormula(f1)
      print(" ) OR ( ")
      print_multisetFormula(f2)
      print(" ) ")
    }
    case FNot(FAnd(FNot(f1),FNot(f2)))   => {
      Console.print(" ( ")
      print_multisetFormula(f1)
      print(" ) OR ( ")
      print_multisetFormula(f2)
      print(" ) ")
    }
    case FNot(f1)  => {
      Console.print(" NOT ( ")
      print_multisetFormula(f1)
      print(" ) ")
    }
    case FAtom(a)  => print_atom(a)
    case FTrue  => Console.print(" TRUE ")
    case FFalse  => Console.print(" FALSE ")
  }

}