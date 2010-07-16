package mapaFun

  sealed abstract class MAPAFunInt
  case class MFIntVar(val i: String) extends MAPAFunInt
  case class MFIntConst (val c: Int) extends MAPAFunInt
  case class MFIPlus(val i1: MAPAFunInt, val i2: MAPAFunInt) extends MAPAFunInt
  case class MFITimes(val c: Int, val i2: MAPAFunInt) extends MAPAFunInt
  case class MFSCard(val s: MAPAFunSet) extends MAPAFunInt
  case class MFMCard(val m: MAPAFunMultiset) extends MAPAFunInt

  sealed abstract class MAPAFunMultiset
  case class MFMSetVar(val m: String) extends MAPAFunMultiset
  case object MFEmptyMSet extends MAPAFunMultiset
  case class MFMUnion(val m1: MAPAFunMultiset, val m2: MAPAFunMultiset) extends MAPAFunMultiset
  case class MFMIntersec(val m1: MAPAFunMultiset, val m2: MAPAFunMultiset) extends MAPAFunMultiset
  case class MFMPlus(val m1: MAPAFunMultiset, val m2: MAPAFunMultiset) extends MAPAFunMultiset
  case class MFMMinus(val m1: MAPAFunMultiset, val m2: MAPAFunMultiset) extends MAPAFunMultiset
  case class MFSetMinus(val m1: MAPAFunMultiset, val m2: MAPAFunMultiset) extends MAPAFunMultiset
  case class MFSSetOf(val m:MAPAFunMultiset) extends MAPAFunMultiset
  case class MFFunction(val f: String, val s: MAPAFunSet) extends MAPAFunMultiset

  sealed abstract class MAPAFunSet
  case class MFSetVar(val s:String) extends MAPAFunSet
  case object MFEmptySet extends MAPAFunSet
  case object MFUnivSet extends MAPAFunSet
  case class MFSUnion(val s1:MAPAFunSet, val s2:MAPAFunSet) extends MAPAFunSet
  case class MFSIntersec(val s1:MAPAFunSet, val s2:MAPAFunSet) extends MAPAFunSet
  case class MFSCompl(val s:MAPAFunSet) extends MAPAFunSet

  sealed abstract class MAPAFunAtom
  case class MFSetEqual(val s1:MAPAFunSet, val s2:MAPAFunSet) extends MAPAFunAtom
  case class MFSetSubset(val s1:MAPAFunSet, val s2:MAPAFunSet) extends MAPAFunAtom
  case class MFMSetEqual(val m1:MAPAFunMultiset, val m2:MAPAFunMultiset) extends MAPAFunAtom
  case class MFMSetSubset(val m1:MAPAFunMultiset, val m2:MAPAFunMultiset) extends MAPAFunAtom
  case class MFIntEqual(val i1:MAPAFunInt, val i2:MAPAFunInt) extends MAPAFunAtom
  case class MFIntLessEqual(val i1:MAPAFunInt, val i2:MAPAFunInt) extends MAPAFunAtom
  case class MFIntDivides(val c:Int, val i:MAPAFunInt) extends MAPAFunAtom

  sealed abstract class MAPAFunFormula
  case class MFAnd(val f1: MAPAFunFormula, val f2: MAPAFunFormula) extends MAPAFunFormula
  case class MFOr(val f1: MAPAFunFormula, val f2: MAPAFunFormula) extends MAPAFunFormula
  case class MFNot(val f: MAPAFunFormula) extends MAPAFunFormula
  case class MFAtom(val a: MAPAFunAtom) extends MAPAFunFormula
