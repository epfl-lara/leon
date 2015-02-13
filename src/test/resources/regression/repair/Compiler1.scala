import leon.lang._
import leon.annotation._
import leon.collection._
import leon._

object Trees {
  abstract class Expr
  case class Plus(lhs: Expr, rhs: Expr) extends Expr
  case class Minus(lhs: Expr, rhs: Expr) extends Expr
  case class LessThan(lhs: Expr, rhs: Expr) extends Expr
  case class And(lhs: Expr, rhs: Expr) extends Expr
  case class Or(lhs: Expr, rhs: Expr) extends Expr
  case class Not(e : Expr) extends Expr
  case class Eq(lhs: Expr, rhs: Expr) extends Expr
  case class Ite(cond: Expr, thn: Expr, els: Expr) extends Expr
  case class IntLiteral(v: Int) extends Expr
  case class BoolLiteral(b : Boolean) extends Expr
}

object Types {
  abstract class Type
  case object IntType extends Type
  case object BoolType extends Type
}


object TypeChecker {
  import Trees._
  import Types._

  def typeOf(e :Expr) : Option[Type] = e match {
    case Plus(l,r) => (typeOf(l), typeOf(r)) match {
      case (Some(IntType), Some(IntType)) => Some(IntType)
      case _ => None()
    }
    case Minus(l,r) => (typeOf(l), typeOf(r)) match {
      case (Some(IntType), Some(IntType)) => Some(IntType)
      case _ => None()
    }
    case LessThan(l,r) => ( typeOf(l), typeOf(r)) match {
      case (Some(IntType), Some(IntType)) => Some(BoolType)
      case _ => None()
    }
    case And(l,r) => ( typeOf(l), typeOf(r)) match {
      case (Some(BoolType), Some(BoolType)) => Some(BoolType)
      case _ => None()
    }
    case Or(l,r) => ( typeOf(l), typeOf(r)) match {
      case (Some(BoolType), Some(BoolType)) => Some(BoolType)
      case _ => None()
    }
    case Not(e) => typeOf(e) match {
      case Some(BoolType) => Some(BoolType)
      case _ => None()
    }
    case Eq(lhs, rhs) => (typeOf(lhs), typeOf(rhs)) match {
      case (Some(t1), Some(t2)) if t1 == t2 => Some(BoolType)
      case _ => None()
    }
    case Ite(c, th, el) => (typeOf(c), typeOf(th), typeOf(el)) match {
      case (Some(BoolType), Some(t1), Some(t2)) if t1 == t2 => Some(t1)
      case _ => None()
    }
    case IntLiteral(_) => Some(IntType)
    case BoolLiteral(_) => Some(BoolType)
  }

  def typeChecks(e : Expr) = typeOf(e).isDefined
}


object Semantics {
  import Trees._
  import Types._
  import TypeChecker._
  
  def semI(t : Expr) : Int = {
    require( typeOf(t) == ( Some(IntType) : Option[Type] ))
    t match {
      case Plus(lhs , rhs) => semI(lhs) + semI(rhs)
      case Minus(lhs , rhs) => semI(lhs) - semI(rhs)
      case Ite(cond, thn, els) => 
        if (semB(cond)) semI(thn) else semI(els)
      case IntLiteral(v)   => v 
    }
  }

  def semB(t : Expr) : Boolean = {
    require( (Some(BoolType): Option[Type]) == typeOf(t))
    t match {
      case And(lhs, rhs ) => semB(lhs) && semB(rhs)
      case Or(lhs , rhs ) => semB(lhs) || semB(rhs)
      case Not(e) => !semB(e)
      case LessThan(lhs, rhs) => semI(lhs) < semI(rhs)
      case Ite(cond, thn, els) => 
        if (semB(cond)) semB(thn) else semB(els)
      case Eq(lhs, rhs) => (typeOf(lhs), typeOf(rhs)) match {
        case ( Some(IntType),  Some(IntType)  ) => semI(lhs) == semI(rhs)
        case ( Some(BoolType), Some(BoolType) ) => semB(lhs) == semB(rhs)
      }
      case BoolLiteral(b) => b
    }
  }
 
  def b2i(b : Boolean) = if (b) 1 else 0

  @induct
  def semUntyped( t : Expr) : Int = { t match {
    case Plus (lhs, rhs) => semUntyped(lhs) + semUntyped(rhs)
    case Minus(lhs, rhs) => semUntyped(lhs) - semUntyped(rhs)
    case And  (lhs, rhs) => if (semUntyped(lhs)!=0) semUntyped(rhs) else 0
    case Or(lhs, rhs ) =>
      if (semUntyped(lhs) == 0) semUntyped(rhs) else 1
    case Not(e) =>
      b2i(semUntyped(e) == 0)
    case LessThan(lhs, rhs) => 
      b2i(semUntyped(lhs) < semUntyped(rhs))
    case Eq(lhs, rhs) => 
      b2i(semUntyped(lhs) == semUntyped(rhs))
    case Ite(cond, thn, els) => 
      if (semUntyped(cond) == 0) semUntyped(els) else semUntyped(thn)
    case IntLiteral(v)  => v 
    case BoolLiteral(b) => b2i(b)
  }} ensuring { res => typeOf(t) match {
    case Some(IntType)  => res == semI(t)
    case Some(BoolType) => res == b2i(semB(t))
    case None() => true
  }}

}


object Desugar {
  import Types._
  import TypeChecker._
  import Semantics.b2i

  abstract class SimpleE 
  case class Plus(lhs : SimpleE, rhs : SimpleE) extends SimpleE
  case class Neg(arg : SimpleE) extends SimpleE
  case class Ite(cond : SimpleE, thn : SimpleE, els : SimpleE) extends SimpleE
  case class Eq(lhs : SimpleE, rhs : SimpleE) extends SimpleE
  case class LessThan(lhs : SimpleE, rhs : SimpleE) extends SimpleE
  case class Literal(i : Int) extends SimpleE

  @induct
  def desugar(e : Trees.Expr) : SimpleE = { e match {
    case Trees.Plus (lhs, rhs) => Neg(desugar(lhs)) // FIXME: Complete nonsense. Leon can't disprove it, uses example...
    case Trees.Minus(lhs, rhs) => Plus(desugar(lhs), Neg(desugar(rhs)))
    case Trees.LessThan(lhs, rhs) => LessThan(desugar(lhs), desugar(rhs))
    case Trees.And  (lhs, rhs) => Ite(desugar(lhs), desugar(rhs), Literal(0)) 
    case Trees.Or   (lhs, rhs) => Ite(desugar(lhs), Literal(1), desugar(rhs))
    case Trees.Not(e) => Ite(desugar(e), Literal(0), Literal(1))
    case Trees.Eq(lhs, rhs) =>
      Eq(desugar(lhs), desugar(rhs))
    case Trees.Ite(cond, thn, els) => Ite(desugar(cond), desugar(thn), desugar(els))
    case Trees.IntLiteral(v)  => Literal(v)
    case Trees.BoolLiteral(b) => Literal(b2i(b))
  }} ensuring { res =>
    ((e, res) passes {
      case Trees.Plus(Trees.IntLiteral(i), Trees.Minus(Trees.IntLiteral(j), Trees.IntLiteral(42))) =>
        Plus(Literal(i), Plus(Literal(j), Neg(Literal(42))))
    }) &&
    sem(res) == Semantics.semUntyped(e)
  }

  def sem(e : SimpleE) : Int = e match {
    case Plus (lhs, rhs) => sem(lhs) + sem(rhs)
    case Ite(cond, thn, els) => if (sem(cond) != 0) sem(thn) else sem(els)
    case Neg(arg) => -sem(arg) 
    case Eq(lhs,rhs) => b2i(sem(lhs) == sem(rhs))
    case LessThan(lhs, rhs) => b2i(sem(lhs) < sem(rhs))
    case Literal(i) => i
  }

}
