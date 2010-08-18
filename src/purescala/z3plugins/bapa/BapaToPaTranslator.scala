package purescala.z3plugins.bapa

import scala.math.{log, min}
import AST._
import NormalForms.{setVariables, rewriteSetRel, simplify}
import z3.scala.Z3Context

class BapaToPaTranslator(z3: Z3Context) {
  //private implicit def rangeToSeq[T](r: IndexedSeq[T]): Seq[T] = r.toSeq

  // returns a PA formula and the number of Venn regions
  def apply(formula: Tree): (Tree, Int) = {
    val setvars = setVariables(formula)
    val formula1 = simplify(rewriteSetRel(formula))
    val (atoms, zeroes, ones) = countCardinalityExpressions(formula1)
    val n0 = findSparsenessBound(atoms - zeroes - ones)
    val n = if (setvars.size <= 30) min(n0 + ones, 1 << setvars.size)
            else (n0 + ones)
    val body = reduce(n)(formula1)
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
    val buf = new scala.collection.mutable.ArrayBuffer[Tree]
    buf += body
    buf ++= nonNegativeCards(n)
    buf ++=  breakSymmetry(n, setvars.toSeq)
    (simplify(Op(AND, buf.toSeq)), n)
  }

  // Create / cache fresh variables
  private val cache = new scala.collection.mutable.HashMap[String,Var]

  private def lookup(varName: String, typ: Type) = cache getOrElse(varName, {
    val freshVar = typ match {
      case BoolType => Var(BoolSymbol(z3.mkFreshConst(varName, z3.mkBoolSort)))
      case IntType => Var(IntSymbol(z3.mkFreshConst(varName, z3.mkIntSort)))
      case SetType => error("no new set variables allowed")
    }
    cache(varName) = freshVar
    freshVar
  })

  private def propVar(k: Int, sym: Symbol): Tree = lookup(sym.name + "_" + k, BoolType) //Symbol.beta(k, id)

  private def intVar(k: Int): Tree = lookup("venn_" + k, IntType)//Symbol.vennSize(k, i)


  // translate BA to PA expression
  // Generate formula of the form
  //    (if st0 then l_k else 0)
  //  where st0 is the result of replacing, in setTerm, the set variables with k-family
  //  of propositional variables, as given by set2prop.
  def ba2pa(setTree: Tree, k: Int): Tree = {
    def set2prop(stree: Tree): Tree = stree match {
      case Var(sym) => propVar(k, sym)
      case Lit(EmptySetLit) => False
      case Lit(FullSetLit) => True
      case Op(COMPL, Seq(set)) => !set2prop(set)
      case Op(UNION, sets) => Op(OR, sets map set2prop)
      case Op(INTER, sets) => Op(AND, sets map set2prop)
      case _ => throw IllegalTerm(setTree)
    }
    set2prop(setTree) ifThenElse (intVar(k), 0)
    //Op(ITE(set2prop(setTerm)), List(intVar(k), 0))
  }

  // reduce QFBAPA formula f to QFPA formula,
  //  introducing only n generic partition cardinality variables
  // pre: formula is in nnf
  def reduce(n: Int) = {
    /*
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
    */
    def reduceTree(tree: Tree): Tree = tree match {
      case Op(CARD, Seq(set)) =>
        if (n == 0) 0
        else Op(ADD, for (k <- 1 to n) yield ba2pa(set, k))
      case Op(op, args) =>
        Op(op, args map reduceTree)
      case _ => tree
    }
    reduceTree _
  }

  // Extractor for countCardinalityExpressions
  private object ExCardLessEqual {
    def unapply(tree: Tree): Option[(Tree, Int)] = tree match {
      case Op(EQ, Seq(Lit(IntLit(card)), Op(CARD, Seq(set)))) => Some((set, card))
      case Op(EQ, Seq(Op(CARD, Seq(set)), Lit(IntLit(card)))) => Some((set, card))
/*GE*/case Op(NOT, Seq(Op(LT, Seq(Lit(IntLit(card)), Op(CARD, Seq(set)))))) => Some((set, card))
//    case Op(LE, Seq(Op(CARD, Seq(set)), Lit(IntLit(card)))) => Some((set, card))
//    case Op(GT, Seq(Lit(IntLit(card)), Op(CARD, Seq(set)))) => Some((set, card - 1))
/*LT*/case Op(LT, Seq(Op(CARD, Seq(set)), Lit(IntLit(card)))) => Some((set, card - 1))
      case _ => None
    }
  }

  def countCardinalityExpressions(tree0: Tree): (Int, Int, Int) = {
    var atoms = 0
    var cardIs0 = 0
    var cardIs1 = 0
    /*
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
    */
    def countTree(tree: Tree): Unit = tree match {
      case ExCardLessEqual(_, 0) => cardIs0 += 1; atoms += 1
      case ExCardLessEqual(_, 1) => cardIs1 += 1; atoms += 1
      case Op(CARD, Seq(Lit(_))) => ()
      case Op(CARD, _) => atoms += 1
      case Op(_, ts) => ts foreach countTree
      case _ => ()
    }
    countTree(tree0)
    (atoms, cardIs0, cardIs1)
  }

  // symmetry_breaking predicate says that
  // propositional variables denote a strictly
  // increasing sequence of regions (lexical ordering)
  private val BREAK_SYMMETRY = true

  def breakSymmetry(n: Int, svars: Seq[Symbol]): Seq[Tree] =
    if (BREAK_SYMMETRY)
      Seq.tabulate(n - 1)(i => mkIndexLess(i + 1)(svars))
    else Nil

  private def mkIndexLess(i: Int) = {
    def rec(sets: Seq[Symbol]): Tree = sets match {
      case Nil => True
      case Seq(s) =>
        // prop less
        val varI = propVar(i, s)
        val varI_1 = propVar(i + 1, s)
        !varI && varI_1
      case s :: ss =>
        // prop equal
        val varI = propVar(i, s)
        val varI_1 = propVar(i + 1, s)
        // TODO: looks like if-and-only-if constraint
//         val equal = (!varI && !varI_1) || (varI && varI_1)
//         rec(Seq(s)) || (equal && rec(ss))
        rec(Seq(s)) || ((varI iff varI_1) && rec(ss))
    }
    rec _
  }

  // Imposes non-negativity for cardinalities of venn regions
  private def nonNegativeCards(n: Int): Seq[Tree] =
    for (i <- 1 to n) yield 0 <= intVar(i)

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
}
