package orderedsets

import AST._
import Primitives._
import Symbol._
import scala.collection.mutable.ListBuffer

case class IllegalTerm(a: Any) extends Exception(a + " should not be present in the formula to be converted.")

object ASTUtil {
  def intvars = variablesOf(_ == IntType)

  def setvars = variablesOf(_ == SetType)

  def propvars = variablesOf(_ == BoolType)

  private def variablesOf(pred: Type => Boolean) = {
    val empty: Set[Symbol] = Set.empty
    def vars(f: Formula): Set[Symbol] = f match {
      case PropVar(sym) if pred(sym.tpe) => Set(sym)
      case True | False => empty
      case Not(f) => vars(f)
      case And(fs) => (empty /: fs) {_ ++ vars(_)}
      case Or(fs) => (empty /: fs) {_ ++ vars(_)}
      case Predicate(_, ts) => (empty /: ts) {_ ++ tvars(_)}
      case _ => empty
    }
    def tvars(t: Term): Set[Symbol] = t match {
      case TermVar(sym) if pred(sym.tpe) => Set(sym)
      case Op(ITE(f), ts) => ((vars(f) /: ts) {_ ++ tvars(_)})
      case Op(_, ts) => (empty /: ts) {_ ++ tvars(_)}
      case _ => empty
    }
    vars _
    //    (f: Formula) => vars(f).toList sort (_.name < _.name)
  }


  def getInfSets(syms: List[Symbol]): Set[Symbol] =
    (Set.empty[Symbol] /: syms) {_ ++ _.infOfList}

  def getSupSets(syms: List[Symbol]): Set[Symbol] =
    (Set.empty[Symbol] /: syms) {_ ++ _.supOfList}


  def filterInfs(syms: List[Symbol]) =
    syms filter {s => s.infOfList != null && !s.infOfList.isEmpty}

  def filterSups(syms: List[Symbol]) =
    syms filter {s => s.supOfList != null && !s.supOfList.isEmpty}


  /**Formula Splitter **/

  type IntVar = Symbol
  type SetVar = Symbol
  type SplitResult = (List[Formula], List[Formula], List[(SetVar, IntVar)], List[(SetVar, IntVar)])

  def split(conj: List[Formula]): SplitResult = {
    val paforms = new ListBuffer[Formula]
    val bapaforms = new ListBuffer[Formula]
    val infs = new ListBuffer[(SetVar, IntVar)]
    val sups = new ListBuffer[(SetVar, IntVar)]

    for (form <- conj) form match {
      case Predicate(EQ, List(TermVar(term), Op(INF, List(TermVar(set))))) => infs += ((set, term))
      case Predicate(EQ, List(TermVar(term), Op(SUP, List(TermVar(set))))) => sups += ((set, term))
      case f if isPA(f) => paforms += f
      case f => bapaforms += f
    }
    (paforms.toList, bapaforms.toList, infs.toList, sups.toList)
  }

  def isPA(form: Formula): Boolean = form match {
    case True | False | PropVar(_) => true
    case Not(f) => isPA(f)
    case And(fs) => fs forall isPA
    case Or(fs) => fs forall isPA
    case Predicate(_: IntOperand, ts) => ts forall isPA
    case _ => false
  }

  def isPA(term: Term): Boolean = term match {
    case TermVar(sym) => sym.isInt
    case Lit(IntLit(_)) => true
    case Op(ITE(f), ts) => isPA(f) && (ts forall isPA)
    case Op(ADD | SUB | MUL | MIN | MAX, ts) => ts forall isPA
    case _ => false
  }

  /* Formula size */

  def sizeOf(form: Formula): Int = form match {
    case True | False | PropVar(_) => 1
    case Not(f) => sizeOf(f) + 1
    case And(fs) => (1 /: (fs map sizeOf))(_ + _)
    case Or(fs) => (1 /: (fs map sizeOf))(_ + _)
    case Predicate(_, ts) => (1 /: (ts map sizeOf))(_ + _)
  }

  def sizeOf(term: Term): Int = term match {
    case TermVar(_) | Lit(_) => 1
    case Op(_, ts) => (1 /: (ts map sizeOf))(_ + _)
  }

  /* Extract formulas from set expressions */

  def analyze(conj: List[Formula], split: SplitResult): List[Formula] = {
    val orderedSets = Set((split._3 ::: split._4).map {_._1}: _*)
    val forms = new ListBuffer[Formula]

    for (form <- conj) form match {
      case Predicate(SEQ, List(s1, s2)) =>
        add(inf(s1), EQ, inf(s2))
        add(sup(s1), EQ, sup(s2))
      case Predicate(SUBSETEQ, List(s1, s2)) =>
        add(inf(s2), LE, inf(s1))
        add(sup(s1), LE, sup(s2))
      case Predicate(EQ, List(Lit(IntLit(0)), Op(CARD, List(s1)))) =>
        if (!inf(s1).isEmpty || !sup(s1).isEmpty)
          return List(False)
      case _ =>
    }

    def add(o1: Option[Term], comp: Logical, o2: Option[Term]) = (o1, o2) match {
      case (Some(t1), Some(t2)) => forms += Predicate(comp, List(t1, t2))
      case _ =>
    }

    def inf(term: Term): Option[Term] = term match {
      case TermVar(sym) if orderedSets(sym) => Some(term.inf)
      case Op(UNION, ts) => ts map inf match {
        case is if is forall {_ isDefined} => Some(Op(MIN, is flatMap {_ toList}))
        case _ => None
      }
      case Op(INTER, ts) => ts map inf match {
        case is if is forall {_ isDefined} => Some(Op(MAX, is flatMap {_ toList}))
        case _ => None
      }
      case Lit(_) | TermVar(_) | Op(COMPL, _) => None
    }
    def sup(term: Term): Option[Term] = term match {
      case TermVar(sym) if orderedSets(sym) => Some(term.sup)
      case Op(UNION, ts) => ts map sup match {
        case is if is forall {_ isDefined} => Some(Op(MAX, is flatMap {_ toList}))
        case _ => None
      }
      case Op(INTER, ts) => ts map sup match {
        case is if is forall {_ isDefined} => Some(Op(MIN, is flatMap {_ toList}))
        case _ => None
      }
      case Lit(_) | TermVar(_) | Op(COMPL, _) => None
    }
    forms.toList
  }

}

/*
object SetsToFormTest extends Application {
  import AST._
  val A = Symbol("A")
  val B = Symbol("B")
  val C = Symbol("C")
  val form = (A subseteq (B ++ C))  && ((B ++ C) subseteq A) && (A.inf === 0) && (B.sup < C.inf)
  
  for (And(fs) <- NormalForms(form)) {
    And(ASTUtil.analyze(fs, ASTUtil.split(fs))).print
  }
}
*/
