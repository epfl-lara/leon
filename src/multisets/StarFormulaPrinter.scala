package multisets

object StarFormulaPrinter {

  def print_QFPAterm(t:TermQFPA):Unit = t match {
    case TConstant(c) => Console.print(c)
    case TVariable(v) => Console.print(v)
    case TPlus(t1, t2) => {
      print_QFPAterm(t1)
      Console.print(" + ")
      print_QFPAterm(t2)
    }
    case TTimes(c, t1)=> {
      Console.print(c + "*")
      print_QFPAterm(t1)
    }
    case TIte(f, t1, t2)=> {
      Console.print("ITE(")
      print_QFPAFormula(f)
      print("; ")
      print_QFPAterm(t1)
      print(", ")
      print_QFPAterm(t2)
      print(")")
    }
  }

  def print_QFPAatom(a:AtomQFPA):Unit = a match {
    case ALeq(t1,t2) => {
      print_QFPAterm(t1)
      Console.print(" =< ")
      print_QFPAterm(t2)
    }
    case AEq(t1,t2) => {
      print_QFPAterm(t1)
      Console.print(" = ")
      print_QFPAterm(t2)
    }
  }

  def print_QFPAFormula(f:QFPAFormula):Unit = f match {
    case QFPAAnd(f1,f2) => {
      Console.print(" ( ")
      print_QFPAFormula(f1)
      print(" ) AND ( ")
      print_QFPAFormula(f2)
      print(" ) ")
    }
    case QFPAOr(f1,f2) => {
      Console.print(" ( ")
      print_QFPAFormula(f1)
      print(" ) OR ( ")
      print_QFPAFormula(f2)
      print(" ) ")
    }
    case QFPANot(f1)  => {
      Console.print(" NOT ( ")
      print_QFPAFormula(f1)
      print(" ) ")
    }
    case QFPAAtom(a)  => print_QFPAatom(a)
    case QFPAFalse => Console.print(" FALSE ")
    case QFPATrue  => Console.print(" TRUE ")
  }


  def print_PAVector(l:List[TermQFPA]):Unit = {
    Console.print(" ( ")
    l.foreach(t => {
      print_QFPAterm(t)
      print(", ")
    })
    print(") ")
  }

  def print_starFormula(f:StarFormula):Unit = f match {
    case StarFormula(f1, l1, l2, f2) => {
      print_QFPAFormula(f1)
      Console.print(" AND ")
      print_PAVector(l1)
      print(" IN { ")
      print_PAVector(l2)
      print(" |  ")
      print_QFPAFormula(f2)
      print(" }*")
    }
  }

}

