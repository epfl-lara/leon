package orderedsets

import scala.collection.mutable.{ListBuffer, HashMap => MutableMap}
import AST._
import Primitives._
import scala.math._

object QFBAPAtoPATranslator {
  private implicit def rangeToList[T](r: IndexedSeq[T]): List[T] = r.toList

  def apply(f: Formula, eqClassNum: Int) = {
    val setvars = ASTUtil.setvars(f)
    val f1 = rewriteSetRel(f)
    val (atoms, zeroes, ones) = countCardinalityExpressions(f1)
    val n0 = findSparsenessBound(atoms - zeroes - ones)
    val n = min(n0 + ones, 1 << setvars.size)
    val body = reduce(n, eqClassNum)(f1)
    /*
    println("In QFBAPAtoPATranslator:")
    f1.print
    println("** Set variables    : " + setvars)
    println("** #atoms           : " + atoms)
    println("** #cards = 0       : " + zeroes)
    println("** #cards <= 1      : " + ones)
    println("** d                : " + (atoms - zeroes - ones))
    println("** sparseness bound : " + n0)
    println("** body             : ")
    body.print
*/
    /*
    println("** Set variables    : " + setvars)
    println("** sparseness bound : " + n0 +" (+ " + ones + ")")
    println("** n                : " + n)
      */
    /* if (setvars.isEmpty)
(True, 0)
else        */
    (And(body :: nonNegativeCards(n, eqClassNum) ::: breakSymmetry(n, setvars.toList).toList), n)
  }

  private def propVar(k: Int, id: TermVar): Formula = Symbol.beta(k, id)

  private def intVar(k: Int, i: Int): Term = Symbol.vennSize(k, i)

  // replace Seteq and Subseteq with Card(...) = 0
  def rewriteSetRel(form: Formula): Formula = form match {
    case And(fs) => And(fs map rewriteSetRel)
    case Or(fs) => Or(fs map rewriteSetRel)
    case Predicate(SEQ, List(s1, s2)) =>
      rewriteSetRel(s1 subseteq s2) && rewriteSetRel(s2 subseteq s1)
    case Predicate(SUBSETEQ, List(s1, s2)) =>
      (s1 ** ~s2).card === 0
    case Not(Predicate(SEQ, List(s1, s2))) =>
      rewriteSetRel(!(s1 subseteq s2)) || rewriteSetRel(!(s2 subseteq s1))
    case Not(Predicate(SUBSETEQ, List(s1, s2))) =>
      (s1 ** ~s2).card > 0
    case Not(f) => !rewriteSetRel(f)
    case Predicate(EQ, List(t1, t2@Op(CARD, _))) =>
      Predicate(EQ, List(t2, t1))
    case _ => form
  }

  // translate BA to PA expression
  // Generate formula of the form
  //    (if st0 then l_k else 0)
  //  where st0 is the result of replacing, in setTerm, the set variables with k-family
  //  of propositional variables, as given by set2prop.
  def ba2pa(setTerm: Term, k: Int, eqClassNum: Int): Term = {
    def set2prop(sterm: Term): Formula = sterm match {
      case id@TermVar(_) => propVar(k, id)
      case Lit(EmptySetLit) => False
      case Lit(FullSetLit) => True
      case Op(COMPL, List(set)) => !set2prop(set)
      case Op(UNION, sets) => Or(sets map set2prop)
      case Op(INTER, sets) => And(sets map set2prop)
      case _ => throw IllegalTerm(setTerm)
    }
    Op(ITE(set2prop(setTerm)), List(intVar(k, eqClassNum), 0))
  }

  // reduce QFBAPA formula f to QFPA formula,
  //  introducing only n generic partition cardinality variables
  // pre: formula is in nnf
  def reduce(n: Int, eqClassNum: Int) = {
    def reduceFormula(form: Formula): Formula = form match {
      case True | False | PropVar(_) => form
      case Not(f) => !reduceFormula(f)
      case And(fs) => And(fs map reduceFormula)
      case Or(fs) => Or(fs map reduceFormula)
      case Predicate(c: IntLogical, ts) => Predicate(c, ts map reduceTerm)
      case _ => throw IllegalTerm(form)
    }
    def reduceTerm(term: Term): Term = term match {
      case Op(CARD, List(set)) =>
        if (n == 0) 0 else Op(ADD, for (k <- 1 to n) yield ba2pa(set, k, eqClassNum))
      case Op(c, ts) =>
        Op(c, ts map reduceTerm)
      case Lit(_) | TermVar(_) => term
    }
    reduceFormula _
  }

  // Extractor for countCardinalityExpressions
  private object ExCardLessEqual {
    def unapply(form: Formula): Option[(Term, Int)] = form match {
      case Predicate(EQ, List(Lit(IntLit(card)), Op(CARD, List(set)))) => Some((set, card))
      case Predicate(EQ, List(Op(CARD, List(set)), Lit(IntLit(card)))) => Some((set, card))
      case Predicate(GE, List(Lit(IntLit(card)), Op(CARD, List(set)))) => Some((set, card))
      case Predicate(LE, List(Op(CARD, List(set)), Lit(IntLit(card)))) => Some((set, card))
      case Predicate(GT, List(Lit(IntLit(card)), Op(CARD, List(set)))) => Some((set, card - 1))
      case Predicate(LT, List(Op(CARD, List(set)), Lit(IntLit(card)))) => Some((set, card - 1))
      case _ => None
    }
  }

  // TODO not equivalent to ml code -.-
  def countCardinalityExpressions(f: Formula): (Int, Int, Int) = {
    var atoms = 0
    var cardIs0 = 0
    var cardIs1 = 0
    def countFormula(form: Formula): Unit = form match {
      case And(fs) => fs foreach countFormula
      case Or(fs) => fs foreach countFormula
      case ExCardLessEqual(_, 0) => cardIs0 += 1; atoms += 1
      case ExCardLessEqual(_, 1) => cardIs1 += 1; atoms += 1
      case Predicate(c: IntLogical, ts) => ts foreach countTerm
      case True | False | PropVar(_) => ()
      case _ => IllegalTerm(form)
    }
    def countTerm(term: Term): Unit = term match {
      case Op(CARD, List(Lit(_))) => ()
      case Op(CARD, _) => atoms += 1
      case Op(_, ts) => ts foreach countTerm
      case _ => ()
    }
    countFormula(f)
    (atoms, cardIs0, cardIs1)
  }

  // symmetry_breaking predicate says that
  // propositional variables denote a strictly
  // increasing sequence of regions (lexical ordering)
  private val BREAK_SYMMETRY = true

  def breakSymmetry(n: Int, svars: List[Symbol]): List[Formula] =
    if (BREAK_SYMMETRY)
      List.tabulate(n - 1)(i => mkIndexLess(i + 1)(svars))
    else Nil

  private def mkIndexLess(i: Int) = {
    def rek(sets: List[Symbol]): Formula = sets match {
      case Nil => True
      case s :: Nil =>
        // prop less
        val varI = propVar(i, s)
        val varI_1 = propVar(i + 1, s)
        !varI && varI_1
      case s :: ss =>
        // prop equal
        val varI = propVar(i, s)
        val varI_1 = propVar(i + 1, s)
        val equal = (!varI && !varI_1) || (varI && varI_1)
        rek(List(s)) || (equal && rek(ss))
    }
    rek _
  }

  // Imposes non-negativity for cardinalities of venn regions
  private def nonNegativeCards(n: Int, eqClassNum: Int) =
    for (i <- 1 to n) yield 0 <= intVar(i, eqClassNum)

  // compute the largest n such that 2^n <= (n+1)^d
  def findSparsenessBound(d: Int) = {
    // Check if 2^n <= (n+1)^d by taking log of both sides
    def small_n(n: Int) = n * log(2) <= d * log(n + 1)
    def binSearch(low: Int, high: Int): Int = {
      if (high <= low + 1) {
        if (small_n(high))
          high
        else
          low
      } else {
        val mid = (high + low) / 2
        if (small_n(mid))
          binSearch(mid, high)
        else
          binSearch(low, mid)
      }
    }
    if (d <= 3)
      d
    else {
      val a0 = d * log(d)
      val b0 = 2 * d * (1 + log(d))
      binSearch(a0.toInt, b0.toInt)
    }
  }

  def rewriteITE(form: Formula): Formula = {
    // The list which defines the termporary variables for ITE expressions.
    // TODO: There will be multiple occurences of Op(ITE(p, trmLst))
    // in the formula. Hence, this is memonized in the mkITEDef function
    // TODO: How are formula compared?
    val definitions = new ListBuffer[Formula]
    val defMap = new MutableMap[Formula, TermVar]()
    var numITE = 0
    def mkITEDef(p: Formula, terms: List[Term]): TermVar = {
      val List(t1, t2) = terms
      val tf: TermVar = Symbol.freshInt
      numITE += 1
      definitions += (p && (tf === t1)) || (!p && (tf === t2))
      defMap(p) = tf
      tf
    }
    def expandTerm(t: Term): Term = t match {
      case Op(ITE(p), terms) => defMap.getOrElse(p, mkITEDef(p, terms))
      case Op(op, terms) => Op(op, terms map expandTerm)
      case _ => t
    }
    def expandForm(f: Formula): Formula = f match {
      case PropVar(_) => f
      case And(fs) => And(fs map expandForm)
      case Or(fs) => Or(fs map expandForm)
      case Not(f) => Not(expandForm(f))
      case Predicate(op: IntLogical, terms) => Predicate(op, terms map expandTerm)
      case _ => throw (new IllegalTerm(f))
    }
    // All ITE terms replaced by fresh variables
    definitions prepend expandForm(form)
    And(definitions.toList)
  }

}
