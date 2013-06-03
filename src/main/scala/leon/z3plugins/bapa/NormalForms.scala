/* Copyright 2009-2013 EPFL, Lausanne */

package purescala.z3plugins.bapa

import z3.scala.Z3Context
import AST._

object NormalForms {
  def boolVariables(tree: Tree) = variables(tree, _ == BoolType)

  def intVariables(tree: Tree) = variables(tree, _ == IntType)

  def setVariables(tree: Tree) = variables(tree, _ == SetType)

  private def variables(tree0: Tree, pred: Type => Boolean): Set[Symbol] = {
    val set = new scala.collection.mutable.HashSet[Symbol]
    def rec(tree: Tree): Unit = tree match {
      case Var(sym) if pred(sym.typ) => set += sym
      case Op(_, ts) => ts foreach rec
      case _ =>
    }
    rec(tree0)
    set.toSet
  }

  // replace Seteq and Subseteq with Card(...) = 0
  def rewriteSetRel(tree: Tree): Tree = tree match {
    case Op(SETEQ, Seq(s1, s2)) =>
      rewriteSetRel(s1 subseteq s2) && rewriteSetRel(s2 subseteq s1)
    case Op(SUBSETEQ, Seq(s1, s2)) =>
      (s1 ** ~s2).card === 0
    case Op(NOT, Seq(Op(SETEQ, Seq(s1, s2)))) =>
      rewriteSetRel(!(s1 subseteq s2)) || rewriteSetRel(!(s2 subseteq s1))
    case Op(NOT, Seq(Op(SUBSETEQ, Seq(s1, s2)))) =>
      (s1 ** ~s2).card > 0
    case Op(op@(AND | OR | NOT), ts) =>
      Op(op, ts map rewriteSetRel)
    case Op(EQ, Seq(t1, t2@Op(CARD, _))) =>
      t2 === t1
    case _ => tree
  }

  def simplify(tree: Tree): Tree = tree match {
    case Lit(_) | Var(_) => tree
    case Op(AND, ts) => flatten(ts, AND, True, False)
    case Op(OR, ts) => flatten(ts, OR, False, True)
    case Op(NOT, Seq(Op(NOT, Seq(t)))) => simplify(t)
    case Op(NOT, Seq(Op(AND, ts))) => simplify(Op(OR, ts map {~_}))
    case Op(NOT, Seq(Op(OR, ts))) => simplify(Op(AND, ts map {~_}))
    case Op(NOT, Seq(t)) => simplify(t) match {
      case Lit(TrueLit) => False
      case Lit(FalseLit) => True
      case tt => !tt
    }
    case Op(INTER, ts) => flatten(ts, INTER, FullSet, EmptySet)
    case Op(UNION, ts) => flatten(ts, UNION, EmptySet, FullSet)
    case Op(COMPL, Seq(Lit(EmptySetLit))) => FullSet
    case Op(COMPL, Seq(Lit(FullSetLit))) => EmptySet
    case Op(COMPL, Seq(Op(COMPL, Seq(t)))) => simplify(t)
    case Op(COMPL, Seq(Op(INTER, ts))) => simplify(Op(UNION, ts map {~_}))
    case Op(COMPL, Seq(Op(UNION, ts))) => simplify(Op(INTER, ts map {~_}))
    case Op(CARD, Seq(Lit(EmptySetLit))) => 0
    //    case Op(ITE, Seq(c, t, e)) => simplify(c) match {
    //      case Lit(TrueLit) => simplify(t)
    //      case Lit(FalseLit) => simplify(e)
    //      case cond => cond ifThenElse (simplify(t), simplify(e))
    //    }
    case Op(ADD, ts) =>
      var intPart = 0
      val acc = new scala.collection.mutable.ListBuffer[Tree]
      for (t <- ts) simplify(t) match {
        case Lit(IntLit(i)) => intPart += i
        case tt => acc += tt
      }
      if (intPart != 0) acc += intPart
      acc.size match {
        case 0 => 0
        case 1 => acc(0)
        case _ => Op(ADD, acc.toSeq)
      }
    case Op(IFF, Seq(t1, t2)) => (simplify(t1), simplify(t2)) match {
      case (tt1, Lit(TrueLit)) => tt1
      case (tt1, Lit(FalseLit)) => simplify(!tt1)
      case (Lit(TrueLit), tt2) => tt2
      case (Lit(FalseLit), tt2) => simplify(!tt2)
      case (tt1, tt2) => tt1 iff tt2
    }
    case Op(EQ, Seq(t1, t2)) => (simplify(t1), simplify(t2)) match {
      case (Lit(l1), Lit(l2)) => if (l1 == l2) True else False
      case (tt1, tt2) => tt1 === tt2
    }
    case Op(op, ts) => Op(op, ts map simplify)
  }

  private def flatten(ts: Seq[Tree], operand: Operand, neutral: Tree, absorbing: Tree) = {
    def flat(t: Tree) = t match {
      case Op(op, ts) if op == operand => ts
      case _ => Seq(t)
    }
    val trees = ts map simplify filterNot {_ == neutral}
    if (trees contains absorbing) absorbing
    else trees flatMap flat match {
      case Nil => neutral
      case Seq(t) => t
      case ts => Op(operand, ts)
    }
  }


  def purify(z3: Z3Context, tree0: Tree) = tree0
  // Used to be that this replaced the cardinality function with the cardinality operator...
  //  def purify(z3: Z3Context, tree0: Tree) = {
  //    var defs: Seq[Tree] = Nil
  //    def rec(tree: Tree): Tree = tree match {
  //      case Op(EQ, Seq(Op(CARD, Seq(s)), t)) => Op(CARD_PRED, Seq(rec(s), rec(t)))
  //      case Op(EQ, Seq(t, Op(CARD, Seq(s)))) => Op(CARD_PRED, Seq(rec(s), rec(t)))
  //      case Op(CARD, Seq(s)) =>
  //        val t = Var(IntSymbol(z3.mkFreshConst("pure", z3.mkIntSort)))
  //        defs = defs :+ Op(CARD_PRED, Seq(rec(s), t))
  //        t
  //      case Op(op, ts) => Op(op, ts map rec)
  //      case Var(_) | Lit(_) => tree
  //    }
  //    val tree1 = rec(tree0)
  //    if (defs.size > 0) Op(AND, defs :+ tree1) else tree1
  //  }
}
