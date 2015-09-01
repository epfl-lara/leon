import leon.lang._
import leon.annotation._
import leon.collection._
import leon._

object Trees {
  abstract class Expr
  case class Plus(lhs: Expr, rhs: Expr) extends Expr
  case class Minus(lhs: Expr, rhs: Expr) extends Expr
  //case class Times(lhs: Expr, rhs: Expr) extends Expr
  case class LessThan(lhs: Expr, rhs: Expr) extends Expr
  case class And(lhs: Expr, rhs: Expr) extends Expr
  case class Or(lhs: Expr, rhs: Expr) extends Expr
  case class Neg(ex : Expr) extends Expr
  //case class Eq(lhs: Expr, rhs: Expr) extends Expr
  case class Ite(cond: Expr, thn: Expr, els: Expr) extends Expr
  case class IntLiteral(v: Int) extends Expr
  case class BoolLiteral(b : Boolean) extends Expr
  case class IntVar(i : Int) extends Expr
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
    /*case Times(l,r) => (typeOf(l), typeOf(r)) match {
      case (Some(IntType), Some(IntType)) => Some(IntType)
      case _ => None()
    }*/
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
    case Neg(ex) => typeOf(ex) match {
      case Some(BoolType) => Some(BoolType)
      case _ => None()
    }
    //case Eq(lhs, rhs) => (typeOf(lhs), typeOf(rhs)) match {
    //  case (Some(t1), Some(t2)) if t1 == t2 => Some(t1)
    //  case _ => None()
    //}
    case Ite(c, th, el) => (typeOf(c), typeOf(th), typeOf(el)) match {
      case (Some(BoolType), Some(t1), Some(t2)) if t1 == t2 => Some(t1)
      case _ => None()
    }
    case IntLiteral(_) => Some(IntType)
    case BoolLiteral(_) => Some(BoolType)
    case IntVar(_) => Some(IntType)
  }

  def typeChecks(e : Expr) = typeOf(e).isDefined
}


object Semantics {
  import Trees._
  import Types._
  import TypeChecker._
  
  def semI(t : Expr, env : Map[Int,Int]) : Int = {
    require( typeOf(t) == ( Some(IntType) : Option[Type] ))
    t match {
      case Plus(lhs , rhs) => semI(lhs, env) + semI(rhs, env)
      case Minus(lhs , rhs) => semI(lhs, env) - semI(rhs, env)
      //case Times(lhs, rhs) => semI(lhs) * semI(rhs)
      case Ite(cond, thn, els) => 
        if (semB(cond, env)) semI(thn, env) else semI(els, env)
      case IntLiteral(v)   => v
      case IntVar(id) => env(id)
    }
  }

  def semB(t : Expr, env : Map[Int,Int]) : Boolean = {
    require( (Some(BoolType): Option[Type]) == typeOf(t))
    t match {
      case And(lhs, rhs ) => semB(lhs, env) && semB(rhs, env)
      case Or(lhs , rhs ) => semB(lhs, env) || semB(rhs, env)
      case Neg(ex) => !semB(ex, env)
      case LessThan(lhs, rhs) => semI(lhs, env) < semI(rhs, env)
      case Ite(cond, thn, els) => 
        if (semB(cond, env)) semB(thn, env) else semB(els, env)
      //case Eq(lhs, rhs) => (typeOf(lhs), typeOf(rhs)) match {
      //  case ( Some(IntType),  Some(IntType)  ) => semI(lhs) == semI(rhs)
      //  case ( Some(BoolType), Some(BoolType) ) => semB(lhs) == semB(rhs)
     // }
      case BoolLiteral(b) => b
    }
  }
 
  def simplify(t : Expr, env : Map[Int,Int]) : Expr = { 
    require(typeChecks(t))
    t match {
      case Plus(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1+i2)
      case Plus(IntLiteral(0), rhs) => rhs
      case Plus(lhs, IntLiteral(0)) => lhs

      case Minus(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1-i2)
      case Minus(lhs, IntLiteral(0)) => lhs

      case LessThan(IntLiteral(i1), IntLiteral(i2)) => BoolLiteral(i1 < i2)

      case And(BoolLiteral(false), _ ) => BoolLiteral(false)
      case And(_, BoolLiteral(false)) => BoolLiteral(false)
      case And(BoolLiteral(true), rhs) => rhs
      case And(lhs, BoolLiteral(true)) => lhs
      
      case Or(BoolLiteral(true), _ ) => BoolLiteral(true)
      case Or(_, BoolLiteral(true)) => BoolLiteral(true)
      case Or(BoolLiteral(false), rhs) => rhs
      case Or(lhs, BoolLiteral(false)) => lhs

      case Neg(BoolLiteral(b)) => BoolLiteral(!b)

      //case Eq(i1, i2) if i1 == i2 => BoolLiteral(true)
      //case Eq(BoolLiteral(true), BoolLiteral(false)) => BoolLiteral(false)
      //case Eq(BoolLiteral(false), BoolLiteral(true)) => BoolLiteral(false)
      //case Eq(IntLiteral(i1), IntLiteral(i2)) if i1 != i2 => BoolLiteral(false)

      case Ite(BoolLiteral(true), thenn, _ ) => thenn
      case Ite(BoolLiteral(false), _, elze ) => elze
  
      case IntVar(id) if env contains id => IntLiteral(env(id))

      case other => other
    }
  } ensuring { res =>
    typeOf(res) == typeOf(t) && (typeOf(res) match {
      case Some(BoolType) => semB(t, env) == semB(res, env)
      case Some(IntType) => semI(t, env) == semI(res, env)
    })
  }

  def simplify2(t : Expr, env : Map[Int,Int]) : Expr = { 
    require(typeChecks(t))
    t match {
      case Plus(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1+i2)
      case Plus(IntLiteral(0), rhs) => rhs
      case Plus(lhs, IntLiteral(0)) => lhs
      case Plus(lhs, Minus(r1, r2)) if lhs == r2 => r1
      case Plus(Minus(l1, l2), rhs) if rhs == l2 => l1

      case Minus(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1-i2)
      case Minus(lhs, IntLiteral(0)) => lhs
      case Minus(Plus(l1,l2), r) if l1 == r => l2
      case Minus(Plus(l1,l2), r) if l2 == r => l1
      case Minus(lhs, rhs) if lhs == rhs => IntLiteral(0)


      case LessThan(IntLiteral(i1), IntLiteral(i2)) => BoolLiteral(i1 < i2)
      case LessThan(lhs, rhs) if lhs == rhs => BoolLiteral(false)

      case And(BoolLiteral(false), _ ) => BoolLiteral(false)
      case And(_, BoolLiteral(false)) => BoolLiteral(false)
      case And(BoolLiteral(true), rhs) => rhs
      case And(lhs, BoolLiteral(true)) => lhs
      case And(Neg(rhs), Neg(lhs)) => Neg(Or(lhs,rhs))
      case And(lhs, rhs) if lhs == rhs => lhs

      case Or(BoolLiteral(true), _ ) => BoolLiteral(true)
      case Or(_, BoolLiteral(true)) => BoolLiteral(true)
      case Or(BoolLiteral(false), rhs) => rhs
      case Or(lhs, BoolLiteral(false)) => lhs
      case Or(Neg(rhs), Neg(lhs)) => Neg(And(lhs,rhs))
      case Or(lhs, rhs) if lhs == rhs => lhs

      case Neg(BoolLiteral(b)) => BoolLiteral(!b)
      case Neg(Neg(ex)) => ex

      //case Eq(i1, i2) if i1 == i2 => BoolLiteral(true)
      //case Eq(BoolLiteral(true), BoolLiteral(false)) => BoolLiteral(false)
      //case Eq(BoolLiteral(false), BoolLiteral(true)) => BoolLiteral(false)
      //case Eq(IntLiteral(i1), IntLiteral(i2)) if i1 != i2 => BoolLiteral(false)

      case Ite(BoolLiteral(true), thenn, _ ) => thenn
      case Ite(BoolLiteral(false), _, elze ) => elze
      case Ite(_, thenn, elze) if thenn == elze => thenn

      case other => other
    }
  } ensuring { res =>
    typeOf(res) == typeOf(t) && (typeOf(res) match {
      case Some(BoolType) => semB(t, env) == semB(res, env)
      case Some(IntType) => semI(t, env) == semI(res, env)
    })
  }

} 
