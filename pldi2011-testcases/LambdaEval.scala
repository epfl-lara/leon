import scala.collection.immutable.Set
import funcheck.Utils._

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
  def ok(expr: Expr): Boolean = expr match {
    case Const(_) => true
    case Lam(_,_) => true
    case Pair(e1, e2) => ok(e1) && ok(e2)
    case Var(_) => false
    case Plus(_,_) => false
    case App(_,_) => false
    case Fst(_) => false
    case Snd(_) => false
  }

  def okPair(p: StoreExprPairAbs): Boolean = p match {
    case StoreExprPair(_, res) => ok(res)
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

  // Find first element in list that has first component 'x' and return its
  // second component, analogous to List.assoc in OCaml
  def find(x: Int, l: List): Expr = {
    require(storeElems(l).contains(x))
    l match {
      case Cons(BindingPair(k,v), is) => if (k == x) v else find(x, is)
    }
  }

  // Evaluator
  def eval(store: List, expr: Expr): StoreExprPairAbs = {
    require(
        freeVars(expr).subsetOf(storeElems(store))
     && (expr match {
          case App(l, _) => eval(store, l) match {
            case StoreExprPair(_, Lam(_,_)) => true
            case _ => false
          }
          case _ => true
        })
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
        /*
        val StoreExprPair(store1, Lam(x, e)) = eval(store, e1) match {
          case StoreExprPair(resS, Lam(resX, resE)) => StoreExprPair(resS, Lam(resX, resE))
        }
        */
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
  } ensuring(res => okPair(res))
  /*ensuring(res => res match {
    case StoreExprPair(_, resExpr) => ok(resExpr)
  }) */

  def property0() : Boolean = {
    okPair(eval(Cons(BindingPair(358, Const(349)), Nil()), Const(1)))
  } holds
}
