import leon.annotation._
import leon.lang._

object LambdaEval { 
  sealed abstract class Expr
  case class Const(value: Int) extends Expr
  case class Plus(lhs: Expr, rhs: Expr) extends Expr
  case class Lam(x: Int, body: Expr) extends Expr
  case class Pair(fst: Expr, snd: Expr) extends Expr
  case class Var(name: Int) extends Expr
  case class App(lhs: Expr, rhs: Expr) extends Expr
  case class Fst(e: Expr) extends Expr
  case class Snd(e: Expr) extends Expr

  // Checks whether the expression is a value
  def isValue(expr: Expr): Boolean = expr match {
    case Const(_) => true
    case Lam(_,_) => true
    case Pair(e1, e2) => isValue(e1) && isValue(e2)
    case Var(_) => false
    case Plus(_,_) => false
    case App(_,_) => false
    case Fst(_) => false
    case Snd(_) => false
  }

  sealed abstract class List
  case class Cons(head: BindingPairAbs, tail: List) extends List
  case class Nil() extends List

  sealed abstract class BindingPairAbs
  case class BindingPair(key: Int, value: Expr) extends BindingPairAbs

  sealed abstract class StoreExprPairAbs
  case class StoreExprPair(store: List, expr: Expr) extends StoreExprPairAbs

  def storeElems(store: List) : Set[Int] = store match {
    case Nil() => Set.empty[Int]
    case Cons(BindingPair(k,_), xs) => Set(k) ++ storeElems(xs)
  }

  def freeVars(expr: Expr) : Set[Int] = expr match {
    case Const(_) => Set.empty[Int]
    case Plus(l,r) => freeVars(l) ++ freeVars(r)
    case Lam(x, bdy) => freeVars(bdy) -- Set(x)
    case Pair(f,s) => freeVars(f) ++ freeVars(s)
    case Var(n) => Set(n)
    case App(l,r) => freeVars(l) ++ freeVars(r)
    case Fst(e) => freeVars(e)
    case Snd(e) => freeVars(e)
  }

  def storeHasValues(store: List): Boolean = store match {
    case Nil() => true
    case Cons(BindingPair(k, v), ss) => isValue(v) && storeHasValues(ss)
  }

  def contains(store: List, key: Int): Boolean = store match {
    case Nil() => false
    case Cons(BindingPair(k, v), xs) => k == key || contains(xs, key)
  }

  // Find first element in list that has first component 'x' and return its
  // second component, analogous to List.assoc in OCaml
  def find(x: Int, l: List): Expr = {
    require(
      contains(l, x) &&
      storeHasValues(l)
    )
    l match {
      case Cons(BindingPair(k,v), is) => if (k == x) v else find(x, is)
    }
  } ensuring(res => isValue(res))

  def wellFormed(store: List, expr: Expr): Boolean = expr match {
    case Const(_) => true
    case Plus(e1, e2) => wellFormed(store, e1) && wellFormed(store, e2) && (eval(store, e1) match {
      case StoreExprPair(_,Const(i1)) =>
        eval(store, e2) match {
          case StoreExprPair(_,Const(i2)) => true
          case _ => false
        }
      case _ => false
    })
    case Lam(x, body) => wellFormed(Cons(BindingPair(x, Const(0)), store), body)
    case Pair(e1, e2) => wellFormed(store, e1) && wellFormed(store, e2)
    case Var(x) => contains(store, x)
    case App(l, r) => wellFormed(store, l) && wellFormed(store, r) && (eval(store, l) match {
      case StoreExprPair(_, Lam(_,_)) => true
      case _ => false
    })
    case Fst(e) => wellFormed(store, e) && (eval(store, e) match {
      case StoreExprPair(_,Pair(e1, e2)) => true
      case _ => false
    })
    case Snd(e) => wellFormed(store, e) && (eval(store, e) match {
      case StoreExprPair(_,Pair(e1, e2)) => true
      case _ => false
    })
  }

  // Evaluator
  def eval(store: List, expr: Expr): StoreExprPairAbs = {
    require(
        wellFormed(store, expr) &&
        storeHasValues(store)
    )

    expr match {
      case Const(i) => StoreExprPair(store, Const(i))
      case Var(x) => StoreExprPair(store, find(x, store))
      case Plus(e1, e2) =>
        val i1 = eval(store, e1) match {
          case StoreExprPair(_, Const(i)) => i
        }
        val i2 = eval(store, e2) match {
          case StoreExprPair(_, Const(i)) => i
        }
        StoreExprPair(store, Const(i1 + i2))
      case App(e1, e2) =>
        val store1 = eval(store, e1) match {
          case StoreExprPair(resS,_) => resS
        }
        val x = eval(store, e1) match {
          case StoreExprPair(_, Lam(resX, _)) => resX
        }
        val e = eval(store, e1) match {
          case StoreExprPair(_, Lam(_, resE)) => resE
        }
        val v2 = eval(store, e2) match {
          case StoreExprPair(_, v) => v
        }
        eval(Cons(BindingPair(x, v2), store1), e)
      case Lam(x, e) => StoreExprPair(store, Lam(x, e))
      case Pair(e1, e2) =>
        val v1 = eval(store, e1) match {
          case StoreExprPair(_, v) => v
        }
        val v2 = eval(store, e2) match {
          case StoreExprPair(_, v) => v
        }
        StoreExprPair(store, Pair(v1, v2))
      case Fst(e) =>
        eval(store, e) match {
          case StoreExprPair(_, Pair(v1, _)) => StoreExprPair(store, v1)
        }
      case Snd(e) =>
        eval(store, e) match {
          case StoreExprPair(_, Pair(_, v2)) => StoreExprPair(store, v2)
        }
    }
  } ensuring(res => res match {
    case StoreExprPair(s, e) => storeHasValues(s) && isValue(e)
  })

  def property0() : Boolean = {
    eval(Cons(BindingPair(358, Const(349)), Nil()), Const(1)) match {
      case StoreExprPair(s, e) => isValue(e)
    }
  } holds
}
