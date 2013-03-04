import leon.lang._
import leon.lang.synthesis._

object Sat {

  sealed abstract class Formula
  case class And(f1: Formula, f2: Formula) extends Formula
  case class Or(f1: Formula, f2: Formula) extends Formula
  case class Not(f: Formula) extends Formula
  case class Var(i: Int) extends Formula

  //vars are numbered from 2 to n+1, and Not(Var(n)) is represented as -n. 1 is true and -1 is false
  sealed abstract class VarList
  case class VarCons(head: Int, tail: VarList) extends VarList
  case class VarNil() extends VarList
  case class VarLit(value: Boolean) extends VarList

  sealed abstract class ClauseList
  case class ClauseCons(head: VarList, tail: ClauseList) extends ClauseList
  case class ClauseNil() extends ClauseList
  case class ClauseLit(value: Boolean) extends ClauseList

  def eval(formula: Formula, trueVars: Set[Int]): Boolean = formula match {
    case Var(n) => if(n == 1) true else if(n == -1) false else trueVars.contains(n)
    case Not(f) => !eval(f, trueVars)
    case And(f1, f2) => eval(f1, trueVars) && eval(f2, trueVars)
    case Or(f1, f2) => eval(f1, trueVars) || eval(f2, trueVars)
  }

  //buggy version of eval
  def evalWrong(formula: Formula, trueVars: Set[Int]): Boolean = formula match {
    case Var(n) => trueVars.contains(n) //bug
    case Not(f) => !eval(f, trueVars)
    case And(f1, f2) => eval(f1, trueVars) && eval(f2, trueVars)
    case Or(f1, f2) => eval(f1, trueVars) || eval(f2, trueVars)
  }

  def evalCnf(clauses: ClauseList, trueVars: Set[Int]): Boolean = clauses match {
    case ClauseCons(cl, cls) => evalClauseCnf(cl, trueVars) && evalCnf(cls, trueVars)
    case ClauseNil() => true
    case ClauseLit(b) => b
  }
  def evalDnf(clauses: ClauseList, trueVars: Set[Int]): Boolean = clauses match {
    case ClauseCons(cl, cls) => evalClauseDnf(cl, trueVars) || evalDnf(cls, trueVars)
    case ClauseNil() => false
    case ClauseLit(b) => b
  }

  //buggy version of evalCnf/Dnf
  def evalCnfWrong(clauses: ClauseList, trueVars: Set[Int]): Boolean = clauses match {
    case ClauseCons(cl, cls) => evalClauseCnf(cl, trueVars) && evalCnf(cls, trueVars)
    case ClauseNil() => false //bug
    case ClauseLit(b) => b
  }
  def evalDnfWrong(clauses: ClauseList, trueVars: Set[Int]): Boolean = clauses match {
    case ClauseCons(cl, cls) => evalClauseDnf(cl, trueVars) || evalDnf(cls, trueVars)
    case ClauseNil() => true //bug
    case ClauseLit(b) => b
  }

  def evalClauseCnf(clause: VarList, trueVars: Set[Int]): Boolean = clause match {
    case VarCons(v, vs) => (if(v < 0) trueVars.contains(-v) else trueVars.contains(v)) || evalClauseCnf(vs, trueVars)
      if(v == 1) true
      else if(v == -1) evalClauseCnf(vs, trueVars)
      else if(v < -1) !trueVars.contains(-v) || evalClauseCnf(vs, trueVars)
      else if(v > 1) trueVars.contains(v) || evalClauseCnf(vs, trueVars)
      else false
    case VarNil() => false
    case VarLit(b) => b
  }
  def evalClauseDnf(clause: VarList, trueVars: Set[Int]): Boolean = clause match {
    case VarCons(v, vs) => {
      if(v == 1) evalClauseDnf(vs, trueVars)
      else if(v == -1) false
      else if(v < -1) !trueVars.contains(-v) && evalClauseDnf(vs, trueVars)
      else if(v > 1) trueVars.contains(v) && evalClauseDnf(vs, trueVars)
      else false
    }
    case VarNil() => true
    case VarLit(b) => b
  }

  //buggy version of evalClauses
  def evalClauseCnfWrong(clause: VarList, trueVars: Set[Int]): Boolean = clause match {
    case VarCons(v, vs) => (if(v < 0) trueVars.contains(-v) else trueVars.contains(v)) || evalClauseCnf(vs, trueVars)
      if(v == 1) true
      else if(v == -1) evalClauseCnf(vs, trueVars)
      else if(v < -1) trueVars.contains(-v) || evalClauseCnf(vs, trueVars) //bug
      else if(v > 1) trueVars.contains(v) || evalClauseCnf(vs, trueVars)
      else false
    case VarNil() => false
    case VarLit(b) => b
  }
  def evalClauseDnfWrong(clause: VarList, trueVars: Set[Int]): Boolean = clause match {
    case VarCons(v, vs) => {
      if(v == 1) evalClauseDnf(vs, trueVars)
      else if(v == -1) false
      else if(v < -1) trueVars.contains(-v) && evalClauseDnf(vs, trueVars) //bug
      else if(v > 1) trueVars.contains(v) && evalClauseDnf(vs, trueVars)
      else false
    }
    case VarNil() => true
    case VarLit(b) => b
  }

  def concatClauses(cll1: ClauseList, cll2: ClauseList): ClauseList = cll1 match {
    case ClauseCons(cl, tail) => ClauseCons(cl, concatClauses(tail, cll2))
    case ClauseNil() => cll2
    case ClauseLit(b) => ClauseCons(VarLit(b), cll2)
  }

  def concatVars(l1: VarList, l2: VarList): VarList = l1 match {
    case VarCons(v, vs) => VarCons(v, concatVars(vs, l2))
    case VarNil() => l2
    case VarLit(b) => if(b) VarCons(1, l2) else VarCons(-1, l2)
  }

  def distributeClause(cl: VarList, cll: ClauseList): ClauseList = cll match {
    case ClauseCons(cl2, cl2s) => ClauseCons(concatVars(cl, cl2), distributeClause(cl, cl2s))
    case ClauseNil() => ClauseNil()
    case ClauseLit(b) => if(b) ClauseCons(VarCons(1, cl), ClauseNil()) else ClauseCons(VarCons(-1, cl), ClauseNil())
  }

  def distribute(cll1: ClauseList, cll2: ClauseList): ClauseList = cll1 match {
    case ClauseCons(cl, cls) => concatClauses(distributeClause(cl, cll2), distribute(cls, cll2))
    case ClauseNil() => cll2
    case ClauseLit(b) => distributeClause(VarLit(b), cll2)
  }

  def negateClauses(cll: ClauseList): ClauseList = cll match {
    case ClauseCons(cl, cls) => ClauseCons(negateVars(cl), negateClauses(cls))
    case ClauseNil() => ClauseNil()
    case ClauseLit(b) => ClauseLit(!b)
  }

  def negateVars(lst: VarList): VarList = lst match {
    case VarCons(v, vs) => VarCons(-v, negateVars(vs))
    case VarNil() => VarNil()
    case VarLit(b) => VarLit(!b)
  }

  def cnfNaive(formula: Formula): ClauseList = formula match {
    case And(f1, f2) => {
      val cnf1 = cnfNaive(f1)
      val cnf2 = cnfNaive(f2)
      concatClauses(cnf1, cnf2)
    }
    case Or(f1, f2) => {
      val cnf1 = cnfNaive(f1)
      val cnf2 = cnfNaive(f2)
      distribute(cnf1, cnf2)
    }
    case Not(And(f1, f2)) => cnfNaive(Or(Not(f1), Not(f2)))
    case Not(Or(f1, f2)) => cnfNaive(And(Not(f1), Not(f2)))
    case Not(Not(f)) => cnfNaive(f)
    case Not(Var(n)) => ClauseCons(VarCons(-n, VarNil()), ClauseNil())
    case Var(n) => ClauseCons(VarCons(n, VarNil()), ClauseNil())
  }
  def dnfNaive(formula: Formula): ClauseList = formula match {
    case And(f1, f2) => {
      val dnf1 = dnfNaive(f1)
      val dnf2 = dnfNaive(f2)
      distribute(dnf1, dnf2)
    }
    case Or(f1, f2) => {
      val dnf1 = dnfNaive(f1)
      val dnf2 = dnfNaive(f2)
      concatClauses(dnf1, dnf2)
    }
    case Not(And(f1, f2)) => dnfNaive(Or(Not(f1), Not(f2)))
    case Not(Or(f1, f2)) => dnfNaive(And(Not(f1), Not(f2)))
    case Not(Not(f)) => dnfNaive(f)
    case Not(Var(n)) => ClauseCons(VarCons(-n, VarNil()), ClauseNil())
    case Var(n) => ClauseCons(VarCons(n, VarNil()), ClauseNil())
  }

  def vars(formula: Formula): Set[Int] = formula match {
    case Var(n) => Set(n)
    case Not(f) => vars(f)
    case And(f1, f2) => vars(f1) ++ vars(f2)
    case Or(f1, f2) => vars(f1) ++ vars(f2)
  }
  def isContradictory(clause: VarList, vars: Set[Int]): Boolean = clause match {
    case VarCons(v, vs) => vars.contains(-v) || vars.contains(-1) || isContradictory(vs, vars ++ Set(v))
    case VarNil() => false
    case VarLit(b) => !b
  }
  def isSatDnf(clauses: ClauseList): Boolean = clauses match {
    case ClauseCons(cl, cls) => !isContradictory(cl, Set.empty) || isSatDnf(cls)
    case ClauseNil() => false
    case ClauseLit(b) => b
  }

  def simplify(formula: ClauseList): ClauseList = formula match {
    case ClauseNil() => ClauseNil()
    case ClauseCons(cl, cls) => simplify(cl) match {
      case VarNil() => ClauseLit(false)
      case VarLit(b) => if(!b) ClauseLit(false) else ClauseCons(VarLit(b), simplify(cls))
      case vs => ClauseCons(vs, simplify(cls))
    }
    case ClauseLit(b) => ClauseLit(b)
  }

  def simplify(vars: VarList): VarList = vars match {
    case VarNil() => VarLit(false)
    case VarLit(b) => VarLit(b)
    case VarCons(1, vs) => VarLit(true)
    case VarCons(-1, vs) => simplify(vs)
    case VarCons(v, vs) => VarCons(v, simplify(vs))
  }

  //for substitute we assume we are dealing with a cnf formula
  def substitute(formula: ClauseList, variable: Int, value: Boolean): ClauseList = formula match {
    case ClauseNil() => ClauseNil()
    case ClauseCons(cl, cls) => ClauseCons(substitute(cl, variable, value), substitute(cls, variable, value))
    case ClauseLit(b) => ClauseLit(b)
  }

  def substitute(vars: VarList, variable: Int, value: Boolean): VarList = vars match {
    case VarNil() => VarNil()
    case VarLit(b) => VarLit(b)
    case VarCons(v, vs) => 
      if     (v == variable && value)   VarLit(true)
      else if(v == variable && !value)  VarCons(-1, substitute(vs, variable, value))
      else if(v == -variable && value)  VarCons(-1, substitute(vs, variable, value))
      else if(v == -variable && !value) VarLit(true)
      else                              VarCons(v, substitute(vs, variable, value))
  }

  def choose(formula: ClauseList): Int = formula match {
    case ClauseCons(varList, cls) => varList match {
      case VarCons(head, vs) => head
      case VarNil() => 0
      case VarLit(b) => 0
    }
    case ClauseNil() => 0
    case ClauseLit(b) => 0
  }

  def dpll(formula: ClauseList): Boolean = formula match {
    case ClauseNil() => true
    case ClauseLit(b) => b
    case _ => {
      val chosenVar = choose(formula)
      val lhs = dpll(simplify(substitute(formula, chosenVar, true)))
      val rhs = dpll(simplify(substitute(formula, chosenVar, false)))
      lhs || rhs
    }
  }



  def property1(formula: Formula, trueVars: Set[Int]): Boolean = {
    val dnfFormula = dnfNaive(formula)
    eval(formula, trueVars) == evalDnf(dnfFormula, trueVars)
  } holds

  def property2(formula: Formula, trueVars: Set[Int]): Boolean = {
    val cnfFormula = cnfNaive(formula)
    eval(formula, trueVars) == evalCnf(cnfFormula, trueVars)
  } holds

  def propertyWrong1(formula: Formula, trueVars: Set[Int]): Boolean = {
    val dnfFormula = dnfNaive(formula)
    isSatDnf(dnfFormula)
  } holds

  def property3(formula: Formula, trueVars: Set[Int]): Boolean = {
    val dnfFormula = dnfNaive(formula)
    if(!isSatDnf(dnfFormula)) eval(formula, trueVars) else true
  } holds

  def property4(formula: Formula): Boolean = {
    val cnfFormula = cnfNaive(formula)
    val dnfFormula = dnfNaive(formula)
    isSatDnf(dnfFormula) == dpll(cnfFormula)
  }


  def main(args: Array[String]) {
    val f1 = And(Var(1), Or(Var(1), Not(Var(2)), Var(3)), Var(2), Not(Var(3)))
    val dnff1 = clauses2list(dnfNaive(f1))
    val vars1 = vars(f1)
    //vars.foreach(v => {


    //})
    println(f1 + " translated in dnf as:\n\t" + dnff1.mkString("\n\t"))
  }

//some non-leon functions to test the program with scala
  object False {
    def apply(): Formula = And(Var(1), Not(Var(1)))
  }
  object True {
    def apply(): Formula = Or(Var(1), Not(Var(1)))
  }
  object Or {
    def apply(fs: Formula*): Formula = fs match {
      case Seq() => False()
      case Seq(f) => f
      case fs => fs.reduceLeft((f1, f2) => Or(f1, f2))
    }
  }
  object And {
    def apply(fs: Formula*): Formula = fs match {
      case Seq() => True()
      case Seq(f) => f
      case fs => fs.reduceLeft((f1, f2) => And(f1, f2))
    }
  }
  def clause2list(cl: VarList): List[Int] = cl match {
    case VarCons(v, vs) => v :: clause2list(vs)
    case VarNil() => Nil
    case VarLit(b) => if(b) List(1) else List(-1)
  }
  def clauses2list(cll: ClauseList): List[List[Int]] = cll match {
    case ClauseCons(cl, cls) => clause2list(cl) :: clauses2list(cls)
    case ClauseNil() => Nil
    case ClauseLit(b) => if(b) List(List(1)) else List(List(-1))
  }
}
