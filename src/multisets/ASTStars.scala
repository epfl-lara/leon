package multisets

  sealed abstract class TermQFPA
  case class TVariable(val v: String) extends TermQFPA
  case class TConstant(val c: Int) extends TermQFPA
  case class TPlus(val t1: TermQFPA, val t2: TermQFPA) extends TermQFPA
  case class TTimes(val c: Int, val t: TermQFPA) extends TermQFPA
  case class TIte(val f: QFPAFormula, val t1: TermQFPA, val t2: TermQFPA) extends TermQFPA

  sealed abstract class AtomQFPA
  case class ALeq(val t1: TermQFPA, val t2: TermQFPA) extends AtomQFPA
  case class AEq(val t1: TermQFPA, val t2: TermQFPA) extends AtomQFPA

  sealed abstract class QFPAFormula
  case class QFPAAnd(val f1: QFPAFormula, val f2: QFPAFormula) extends QFPAFormula
  case class QFPAOr(val f1: QFPAFormula, val f2: QFPAFormula) extends QFPAFormula
  case class QFPANot(val f: QFPAFormula) extends QFPAFormula
  case class QFPAAtom(val a: AtomQFPA) extends QFPAFormula
  case object QFPAFalse extends QFPAFormula
  case object QFPATrue extends QFPAFormula

  // f1 & l1 \in {l2 | f2}*
  case class StarFormula(val f1: QFPAFormula, val l1: List[TermQFPA], val l2: List[TermQFPA], val f2: QFPAFormula)
