package multisets

import purescala.Trees._
import purescala.TypeTrees._

import scala.collection.mutable.Set



object MainAST2MultisetsTranslator {


  def translate(expr: Expr) : Option[(Formula, Set[String])] = {
    case class CantTranslateExpression() extends Exception


   def multisetTranslate(m: Expr): (Multiset, Set[String]) = m match {
     case v @ Variable(id) if v.getType.isInstanceOf[MultisetType] => (MVariable(id.uniqueName), Set.empty[String])
     case EmptyMultiset(_) => (MEmpty, Set.empty[String])
     case MultisetIntersection(m1, m2) => {
        val p1 = multisetTranslate(m1)
        val p2 = multisetTranslate(m2)
        (MIntersection(p1._1, p2._1), p1._2 ++ p2._2)
     }
     case MultisetUnion(m1, m2) => {
        val p1 = multisetTranslate(m1)
        val p2 = multisetTranslate(m2)
        (MUnion(p1._1, p2._1), p1._2 ++ p2._2)
     }
     case MultisetPlus(m1, m2) => {
        val p1 = multisetTranslate(m1)
        val p2 = multisetTranslate(m2)
        (MPlus(p1._1, p2._1), p1._2 ++ p2._2)
     }
     case MultisetDifference(m1, m2) => {
        val p1 = multisetTranslate(m1)
        val p2 = multisetTranslate(m2)
        (MMinus(p1._1, p2._1), p1._2 ++ p2._2)
     }
     case MultisetToSet(m1) => {
        val p1 = multisetTranslate(m1)
        (MSetOf(p1._1), p1._2)
     }
  }

  def termOutTranslate(exp: Expr): (TermOut, Set[String]) = exp match {
    case v @ Variable(id) if v.getType == Int32Type => (TOVariable(id.uniqueName), Set.empty[String])
    case IntLiteral(v) => (TOConstant(v), Set.empty[String])
    case MultisetCardinality(m) => {
      val mN = multisetTranslate(m)
      (TOCard(mN._1), mN._2)
    }
    case SetCardinality(s) => {
      val mN = setTranslate(s)
      (TOCard(mN._1), mN._2)
    }
    case Plus(t1, t2) => {
      val p1 = termOutTranslate(t1)
      val p2 = termOutTranslate(t2)
      (TOPlus(p1._1, p2._1), p1._2 ++ p2._2)
    }
    case Minus(t1, t2) => {
      val p1 = termOutTranslate(t1)
      val p2 = termOutTranslate(t2)
      (TOPlus(p1._1, TOTimes(-1, p2._1)), p1._2 ++ p2._2)
    }
  }

   def setTranslate(s: Expr): (Multiset, Set[String]) = s match {
     case v @ Variable(id) if v.getType.isInstanceOf[SetType] => (MVariable(id.uniqueName), Set(id.uniqueName))
     case EmptySet(_) => (MEmpty, Set.empty[String])
     case SetIntersection(s1, s2) => {
        val p1 = setTranslate(s1)
        val p2 = setTranslate(s2)
        (MIntersection(p1._1, p2._1), p1._2 ++ p2._2)
     }
     case SetUnion(s1, s2) => {
        val p1 = setTranslate(s1)
        val p2 = setTranslate(s2)
        (MUnion(p1._1, p2._1), p1._2 ++ p2._2)
     }
     case SetDifference(s1, s2) => {
        val p1 = setTranslate(s1)
        val p2 = setTranslate(s2)
        (MMinus(p1._1, p2._1), p1._2 ++ p2._2)
     }
     case MultisetToSet(m1) => {
        val p1 = multisetTranslate(m1)
        (MSetOf(p1._1), p1._2)
     }
  }






  def createFormulaFromAndSeq(fs: Seq[Formula]): Formula = {
    val f = if (fs.isEmpty) FTrue else {
      var ft = fs.head
      val t = fs.tail
      t.foreach(f1 => ft = FAnd(f1, ft))
      ft
    }
    f
  }

  def createFormulaFromOrSeq(fs: Seq[Formula]): Formula = {
    val f = if (fs.isEmpty) FTrue else {
      var ft = fs.head
      val t = fs.tail
      t.foreach(f1 => ft = FOr(f1, ft))
      ft
    }
    f
  }


  def createUnionOfAllSets(s: Seq[Set[String]]): Set[String] = {
    val sr = if (s.isEmpty) Set.empty[String] else {
      var h = s.head
      val t = s.tail
      t.foreach(v => h = h ++ v)
      h
    }
    sr
  }

/*
  case class UMinus(expr: Expr) extends Expr with FixedType { 
    val fixedType = Int32Type
  }
  case class Times(lhs: Expr, rhs: Expr) extends Expr with FixedType { 
    val fixedType = Int32Type
  }
  case class Division(lhs: Expr, rhs: Expr) extends Expr with FixedType { 
    val fixedType = Int32Type
  } */


  def rec(ex: Expr) : (Formula, Set[String]) = ex match {
    case MultisetEquals(m1,m2) => {
      val p1 = multisetTranslate(m1)
      val p2 = multisetTranslate(m2)
      (FAtom(AEqual(p1._1, p2._1)), p1._2 ++ p2._2)
    }
    case SubmultisetOf(m1,m2) => {
      val p1 = multisetTranslate(m1)
      val p2 = multisetTranslate(m2)
      (FAtom(ASubset(p1._1, p2._1)), p1._2 ++ p2._2)
    }
    case SetEquals(s1,s2) => {
      val p1 = setTranslate(s1)
      val p2 = setTranslate(s2)
      (FAtom(AEqual(p1._1, p2._1)), p1._2 ++ p2._2)
    }
    case SubsetOf(s1,s2) => {
      val p1 = setTranslate(s1)
      val p2 = setTranslate(s2)
      (FAtom(ASubset(p1._1, p2._1)), p1._2 ++ p2._2)
    }
    case And(expS) => {
      val pl = expS.map(e => rec(e))
      val fl = pl.map(p => p._1)
      val sl = pl.map(p => p._2)
      val f1 = createFormulaFromAndSeq(fl)
      val s1 = createUnionOfAllSets(sl)
      (f1, s1)
    }
    case Or(expS) => {
      val pl = expS.map(e => rec(e))
      val fl = pl.map(p => p._1)
      val sl = pl.map(p => p._2)
      val f1 = createFormulaFromOrSeq(fl)
      val s1 = createUnionOfAllSets(sl)
      (f1, s1)
    }
    case Iff(f1, f2) => {
      val p1 = rec(f1)
      val p2 = rec(f2)
      (FOr(FAnd(FNot(p1._1), FNot(p2._1)), FAnd(p1._1, p2._1)), p1._2 ++ p2._2)
    }
    case Implies(f1, f2) => {
      val p1 = rec(f1)
      val p2 = rec(f2)
      (FOr(FNot(p1._1), p2._1), p1._2 ++ p2._2)
    }
    case Not(f1) => {
      val p1 = rec(f1)
      (FNot(p1._1), p1._2)
    }
    case LessThan(t1, t2) => {
      val p1 = termOutTranslate(t1)
      val p2 = termOutTranslate(t2)
      (FAnd(FAtom(AAtomOut(AOLeq(p1._1, p2._1))), FNot(FAtom(AAtomOut(AOEq(p1._1, p2._1))))), p1._2 ++ p2._2)
    }
    case GreaterThan(t1, t2) => rec(LessThan(t2, t1))
    case LessEquals(t1, t2) => {
      val p1 = termOutTranslate(t1)
      val p2 = termOutTranslate(t2)
      (FAtom(AAtomOut(AOLeq(p1._1, p2._1))), p1._2 ++ p2._2)
    }
    case GreaterEquals(t1, t2) => rec(LessEquals(t2, t1))
    case Equals(t1, t2) => {
      val p1 = termOutTranslate(t1)
      val p2 = termOutTranslate(t2)
      (FAtom(AAtomOut(AOEq(p1._1, p2._1))), p1._2 ++ p2._2)
    }
    case unhandled => {
      Global.reporter.warning("Can't translate this in Munch : " + unhandled)
      throw CantTranslateExpression()
    }
    }


    try {
      Some(rec(expandLets(expr)))
    } catch {
      case CantTranslateExpression() => None
    }

  }


}

