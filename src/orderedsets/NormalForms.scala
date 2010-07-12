package orderedsets

object NormalForms {
  import AST._
  import Primitives._

  // chains all transformations
  def apply(formula: Formula) = dnf(nnf(formula)) map rewrite map And

  /**Normal form transformations **/

  type Conjunction = List[Formula]
  type DNF = Stream[Conjunction]

  // Complete dnf transformation
  def dnf(f: Formula): DNF = f match {
    case And(Nil) => Stream(Nil)
    case And(c :: Nil) => dnf(c)
    case And(c :: cs) =>
      for (conj1 <- dnf(c); conj2 <- dnf(And(cs)))
      yield conj1 ++ conj2
    case Or(Nil) => Stream(List(False))
    case Or(d :: Nil) => dnf(d)
    case Or(d :: ds) => dnf(d) append dnf(Or(ds))
    case Not(And(_) | Or(_)) =>
      // dnf(nnf(f))
      error("Not in negated normal form !")
    case _ => Stream(f :: Nil)
  }


  // Partial dnf transformation
  // The relevant atoms for the ordered decision procedure are in dnf form
  def pdnf(f: Formula): DNF = if (isAtom(f)) Stream(f :: Nil) else f match {
    case And(Nil) => Stream(Nil)
    case And(c :: Nil) => pdnf(c)
    case And(c :: cs) =>
      for (conj1 <- pdnf(c); conj2 <- pdnf(And(cs)))
      yield conj1 ++ conj2
    case Or(Nil) => Stream(List(False))
    case Or(d :: Nil) => pdnf(d)
    case Or(d :: ds) => pdnf(d) append pdnf(Or(ds))
    case Not(And(_) | Or(_)) =>
      // pdnf(nnf(f))
      error("Not in negated normal form !")
    case _ => Stream(f :: Nil)
  }

  private def isAtom(f: Formula): Boolean = f match {
    case True | False | PropVar(_) => true
    case Not(f) => isAtom(f)
    case And(fs) => fs forall isAtom
    case Or(fs) => fs forall isAtom
    case Predicate(SELEM | SLT, _) => false
    case Predicate(_, fs) => fs forall isAtom
  }

  private def isAtom(t: Term): Boolean = t match {
    case Op(LRANGE | TAKE | INF | SUP, _) => false
    case _ => true
  }


  private def flatAnd(f: Formula) = f match {
    case And(fs) => fs
    case _ => List(f)
  }

  private def flatOr(f: Formula) = f match {
    case Or(fs) => fs
    case _ => List(f)
  }

  // Negated normal form with and/or/union/inter/plus/times flattening
  def nnf(form: Formula): Formula = form match {
    case True | False | PropVar(_) | Not(PropVar(_)) => form
    case And(fs) =>
      val formulas = fs map nnf filterNot {_ == True}
      if (formulas contains False) False
      else formulas flatMap flatAnd match {
        case Nil => True
        case f :: Nil => f
        case fs => And(fs)
      }
    case Or(fs) =>
      val formulas = fs map nnf filterNot {_ == False}
      if (formulas contains True) True
      else formulas flatMap flatOr match {
        case Nil => False
        case f :: Nil => f
        case fs => Or(fs)
      }
    case Predicate(op, terms) =>
      Predicate(op, terms map nnf)
    case Not(Not(p)) => nnf(p)
    case Not(And(fs)) => nnf(Or(fs map Not))
    case Not(Or(fs)) => nnf(And(fs map Not))
    case Not(True) => False
    case Not(False) => True
    case Not(Predicate(op: IntLogical, terms)) =>
      Predicate(negate(op), terms map nnf)
    case Not(Predicate(op, terms)) =>
      Not(Predicate(op, terms map nnf))
  }

  private def flatten(ts: List[Term], prim: NonLogical, neutral: Term, absorbing: Term) = {
    def flat(t: Term) = t match {
      case Op(p, ts) if p == prim => ts
      case _ => List(t)
    }
    val terms = ts map nnf filterNot {_ == neutral}
    if (terms contains absorbing) absorbing
    else terms flatMap flat match {
      case Nil => neutral
      case List(t) => t
      case ts => Op(prim, ts)
    }
  }

  def nnf(term: Term): Term = term match {
    case Op(ITE(f), ts@List(t1, t2)) => nnf(f) match {
      case True => nnf(t1)
      case False => nnf(t2)
      case f0 => Op(ITE(f0), ts map nnf)
    }
    case Op(INTER, ts) => flatten(ts, INTER, fullset, emptyset)
    case Op(UNION, ts) => flatten(ts, UNION, emptyset, fullset)
    case Op(ADD, ts) => flatten(ts, ADD, zero, null)
    case Op(MUL, ts) => flatten(ts, MUL, one, zero)
    case Op(COMPL, List(Lit(EmptySetLit))) => fullset
    case Op(COMPL, List(Lit(FullSetLit))) => emptyset
    case Op(COMPL, List(Op(COMPL, List(t)))) => nnf(t)
    case Op(COMPL, List(Op(INTER, ts))) => nnf(Op(UNION, ts map {~_}))
    case Op(COMPL, List(Op(UNION, ts))) => nnf(Op(INTER, ts map {~_}))
    case Op(CARD, List(t)) => nnf(t) match {
      case Lit(EmptySetLit) => zero
      //case Lit(FullSetLit) => maxC
      case t => Op(CARD, List(t))
    }
    case Op(prim, ts) => Op(prim, ts map nnf)
    case Lit(_) | TermVar(_) => term
  }


  /* Rewrite compound primitives and make INF/SUP operations pure */

  def rewrite(formulas: Conjunction): Conjunction = formulas flatMap rewrite

  def rewrite(f: Formula): Conjunction = f match {
    case Predicate(SELEM, List(t, _s)) =>
      rewritePure(t, tf => rewriteNonPure(_s, s => {
        val af = Symbol.freshSet
        (af.card === 1) :: (tf === af.inf) :: (tf === af.sup) ::
                (af subseteq s) :: Nil
      }))
    case Not(Predicate(SELEM, List(t, s))) =>
      rewrite(Predicate(SELEM, List(t, ~s)))

    case Predicate(SLT, args) =>
      rewritePure_*(args, xs => {
        val List(s1, s2) = xs
        val supf = Symbol.supOf(s1)
        val inff = Symbol.infOf(s2)
        (supf < inff) :: (supf === s1.sup) :: (inff === s2.inf) :: Nil
      })
    case Not(Predicate(SLT, args)) =>
      rewritePure_*(args, xs => (xs: @unchecked) match {
        case s1 :: s2 :: Nil =>
          val supf = Symbol.supOf(s1)
          val inff = Symbol.infOf(s2)
          (supf >= inff) :: (supf === s1.sup) :: (inff === s2.inf) :: Nil
      })
    case Predicate(EQ, List(t, Op(op@(SUP | INF), List(s)))) =>
      rewritePure(t, tf =>
        rewritePure(s, sf =>
          (tf === Op(op, List(sf))) :: Nil
          ))
    case Predicate(EQ, List(Op(op@(SUP | INF), List(s)), t)) =>
      rewritePure(s, sf =>
        rewritePure(t, tf =>
          (tf === Op(op, List(sf))) :: Nil
          ))
    case Predicate(comp, terms) =>
      rewriteNonPure_*(terms, ts => Predicate(comp, ts) :: Nil)

    case Not(Predicate(comp, terms)) =>
      rewriteNonPure_*(terms, ts => Not(Predicate(comp, ts)) :: Nil)

    case And(_) | Or(_) if !isAtom(f) =>
      error("A simplified conjunction cannot contain " + f)

    case _ => List(f)
  }

  private def rewritePure(term: Term, ctx: TermVar => Conjunction) = term match {
    case id@TermVar(_) => ctx(id)

    case Op(_: SetOperand, _) | Lit(EmptySetLit | FullSetLit) =>
      val sf = Symbol.freshSet
      rewriteNonPure(term, s =>
        if (s.isInstanceOf[TermVar]) ctx(s.asInstanceOf[TermVar])
        else (sf seq s) :: ctx(sf))
    case _ =>
      val tf = Symbol.freshInt
      rewriteNonPure(term, t =>
        if (t.isInstanceOf[TermVar]) ctx(t.asInstanceOf[TermVar])
        else (tf === t) :: ctx(tf))
  }

  private def rewriteNonPure(term: Term, ctx: Term => Conjunction): Conjunction = term match {
    case Op(op@(INF | SUP), List(s)) =>
      rewritePure(s, sf => {
        val tf = Symbol.freshInt
        (tf === Op(op, List(sf))) :: ctx(tf)
      })

    case Op(SINGLETON, List(t)) =>
      val sf = Symbol.freshSet
      rewritePure(t, tf => {
        (sf.card === 1) :: (tf === sf.inf) :: (tf === sf.sup) :: ctx(sf)
      })

    case Op(TAKE, List(t, s)) =>
      val af = Symbol.freshSet
      rewritePure(s -- af, bf => {
        val form = (af.inf === s.inf) :: (af slt bf) :: (bf.sup === s.sup) :: Nil
        (t === af.card) :: (af subseteq s) :: rewrite(form) ::: ctx(af)
      })

    case Op(LRANGE, List(t1, t2, s)) =>
      val s1 = Symbol.freshSet
      val s2 = Symbol.freshSet
      val s3 = Symbol.freshSet
      val s4 = Symbol.freshSet
      rewritePure(s, sf => {
        val form = (sf.inf === s1.inf) :: (s1 slt s2) :: (s2.sup === sf.sup) :: Nil
        val formIn = (s1.inf === s3.inf) :: (s3 slt s4) :: (s4.sup === s1.sup) :: Nil
        (s1.card === t2) :: (s3.card === (t1 - 1)) :: (s1 ++ s2 seq sf) :: (s3 ++ s4 seq s1) :: rewrite(form ::: formIn) ::: ctx(s4)
      })

    case Op(op, terms) =>
      rewriteNonPure_*(terms, ts => ctx(Op(op, ts)))

    case _ => ctx(term)
  }

  private def rewritePure_*(trees: List[Term], ctx: List[TermVar] => Conjunction): Conjunction =
    trees match {
      case Nil => ctx(Nil)
      case t :: ts =>
        rewritePure(t, tSym => rewritePure_*(ts, tSyms => ctx(tSym :: tSyms)))
    }

  private def rewriteNonPure_*(trees: List[Term], ctx: List[Term] => Conjunction): Conjunction =
    trees match {
      case Nil => ctx(Nil)
      case t :: ts =>
        rewriteNonPure(t, tSym => rewriteNonPure_*(ts, tSyms => ctx(tSym :: tSyms)))
    }

}
