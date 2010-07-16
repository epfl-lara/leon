package multisets

  sealed abstract class Multiset
  case class MVariable(val v: String) extends Multiset
  case object MEmpty extends Multiset
  case class MUnion(val m1: Multiset, val m2: Multiset) extends Multiset
  case class MIntersection(val m1: Multiset, val m2: Multiset) extends Multiset
  case class MPlus(val m1: Multiset, val m2: Multiset) extends Multiset
  case class MMinus(val m1: Multiset, val m2: Multiset) extends Multiset
  case class MSetMinus(val m1: Multiset, val m2: Multiset) extends Multiset
  case class MSetOf(val m: Multiset) extends Multiset

  sealed abstract class TermIn
  case class TIMultiplicity(val v: String) extends TermIn
  case class TIConstant(val c: Int) extends TermIn
  case class TIPlus(val t1: TermIn, val t2: TermIn) extends TermIn
  case class TITimes(val c: Int, val t: TermIn) extends TermIn
  case class TIIte(val f: FormulaIn, val t1: TermIn, val t2: TermIn) extends TermIn

  sealed abstract class AtomIn
  case class AILeq(val t1: TermIn, t2: TermIn) extends AtomIn
  case class AIEq(val t1: TermIn, t2: TermIn) extends AtomIn

  sealed abstract class FormulaIn
  case class FIAtom(val a: AtomIn) extends FormulaIn
  case class FIAnd(val f1: FormulaIn, val f2: FormulaIn) extends FormulaIn
  case class FIOr(val f1: FormulaIn, val f2: FormulaIn) extends FormulaIn
  case class FINot(val f: FormulaIn) extends FormulaIn
  case object FITrue extends FormulaIn
  case object FIFalse extends FormulaIn


  sealed abstract class TermOut
  case class TOConstant(val c: Int) extends TermOut
  case class TOVariable(val v: String) extends TermOut
  case class TOCard(val m: Multiset) extends TermOut
  case class TOPlus(val t1: TermOut, val t2: TermOut) extends TermOut
  case class TOTimes(val c: Int, val t: TermOut) extends TermOut
  case class TOIte(val f: FormulaOut, val t1: TermOut, val t2: TermOut) extends TermOut

  sealed abstract class AtomOut
  case class AOLeq(val t1: TermOut, t2: TermOut) extends AtomOut
  case class AOEq(val t1: TermOut, t2: TermOut) extends AtomOut
  case class AOSum(val v1: List[TermOut], val f: FormulaIn, val v2: List[TermIn]) extends AtomOut

  sealed abstract class FormulaOut
  case class FOAtom(val a: AtomOut) extends FormulaOut
  case class FOAnd(val f1: FormulaOut, val f2: FormulaOut) extends FormulaOut
  case class FOOr(val f1: FormulaOut, val f2: FormulaOut) extends FormulaOut
  case class FONot(val f: FormulaOut) extends FormulaOut
  case object FOTrue extends FormulaOut
  case object FOFalse extends FormulaOut

  sealed abstract class Atom
  case class AEqual(val m1:Multiset, val m2:Multiset) extends Atom
  case class ASubset(val m1:Multiset, val m2:Multiset) extends Atom
  case class AForAllElem(val f:FormulaIn) extends Atom
  case class AAtomOut(val a:AtomOut) extends Atom

  sealed abstract class Formula
  case class FAnd(val f1: Formula, val f2: Formula) extends Formula
  case class FOr(val f1: Formula, val f2: Formula) extends Formula
  case class FNot(val f: Formula) extends Formula
  case class FAtom(val a: Atom) extends Formula
  case object FTrue extends Formula
  case object FFalse extends Formula
