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
  case class Let(id : Int, e : Expr, body : Expr) extends Expr
  case class Var(id : Int) extends Expr
}

object Types {
  abstract class Type
  case object IntType extends Type
  case object BoolType extends Type
}

object Environments {
  val empty = Map.empty[Int,(Trees.Expr,Types.Type)]
}

object TypeChecker {
  import Trees._
  import Types._

  def typeOf(e :Expr)(implicit env : Map[Int, (Expr,Type)]) : Option[Type] = e match {
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
    case Let(i,e,body) => typeOf(e) match {
      case None() => None()
      case Some(tp) => typeOf(body)(env updated (i, (e,tp)))     
    }
    case Var(id) => if (env contains id) Some(env(id)._2) else None()
  }

  def typeChecks(e : Expr)= typeOf(e)(Environments.empty).isDefined
/*
  def closed(t : Expr)(implicit env : Map[Int,(Expr,Type)]) : Boolean = {
    require(typeChecks(t))
    t match {
      case Var(id) => env contains id
      case Let(id, e, body) => closed(e) && closed(body)(env updated (id, (e,typeOf(e).get)))
      case Plus(l,r) => closed(l) && closed(r)
      case Minus(l,r) => closed(l) && closed(r)
      case LessThan(l,r) => closed(l) && closed(r)
      case And(l,r) => closed(l) && closed(r)
      case Or(l,r) => closed(l) && closed(r)
      case Neg(ex) => closed(ex)
      case Ite(c, th, el) => closed(c) && closed(th) && closed(el)
      case IntLiteral(_) => true
      case BoolLiteral(_) => true
    }
  }*/

//  def closed(t : Expr) : Boolean = closed(t)(Map[Int,Expr]())
}


object Semantics {
  import Trees._
  import Types._
  import TypeChecker._
  
  def semI(t : Expr)(implicit env : Map[Int,(Expr,Type)]) : Int = {
    require( typeOf(t).isDefined && typeOf(t).get == IntType )
    t match {
      case Plus(lhs , rhs) => semI(lhs) + semI(rhs)
      case Minus(lhs , rhs) => semI(lhs) - semI(rhs)
      //case Times(lhs, rhs) => semI(lhs) * semI(rhs)
      case Ite(cond, thn, els) => 
        if (semB(cond)) semI(thn) else semI(els)
      case IntLiteral(v)  => v
      case Let(id, e, bd) => 
        typeOf(e) match {
          case Some(IntType)  => semI(bd)(env updated (id, (IntLiteral(semI(e)), IntType)))
          case Some(BoolType) => semI(bd)(env updated (id, (BoolLiteral(semB(e)), BoolType)))
        }
      case Var(id) => semI(env(id)._1)
    }
  }

  def semB(t : Expr)(implicit env :Map[Int,(Expr,Type)]) : Boolean = {
    require( typeOf(t).isDefined && typeOf(t).get == BoolType )
    t match {
      case And(lhs, rhs ) => semB(lhs) && semB(rhs)
      case Or(lhs , rhs ) => semB(lhs) || semB(rhs)
      case Neg(ex) => !semB(ex)
      case LessThan(lhs, rhs) => semI(lhs) < semI(rhs)
      case Ite(cond, thn, els) => 
        if (semB(cond)) semB(thn) else semB(els)
      case Let(id, e, bd) => 
        typeOf(e) match {
          case Some(IntType)  => semB(bd)(env updated (id, (IntLiteral(semI(e)), IntType)))
          case Some(BoolType) => semB(bd)(env updated (id, (BoolLiteral(semB(e)), BoolType)))
        }
      case Var(id) => semB(env(id)._1)
      //case Eq(lhs, rhs) => (typeOf(lhs), typeOf(rhs)) match {
      //  case ( Some(IntType),  Some(IntType)  ) => semI(lhs) == semI(rhs)
      //  case ( Some(BoolType), Some(BoolType) ) => semB(lhs) == semB(rhs)
     // }
      case BoolLiteral(b) => b
    }
  }
}

object Simplifier {
  import Types._
  import Trees._
  import TypeChecker._
  import Semantics._

  def simplify(t : Expr)(implicit env : Map[Int,(Expr,Type)]) : Expr = { 
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
  
      case Var(id) => env(id)._1 // Think about this

      case other => other
    }
  } ensuring { res =>
    typeOf(res) == typeOf(t) && (typeOf(res) match {
      case Some(BoolType) => semB(t) == semB(res)
      case Some(IntType) => semI(t) == semI(res)
    })
  }

  /*
  def simplify(t : Expr)(implicit env : Map[Int,(Expr,Type)]) : Expr = { 
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
  
      case Var(id) => env(id)._1 // Think about this

      case other => other
    }
  } ensuring { res =>
    typeOf(res) == typeOf(t) && (typeOf(res) match {
      case Some(BoolType) => semB(t) == semB(res)
      case Some(IntType) => semI(t) == semI(res)
    })
  }*/


  def simplify2(t : Expr)(implicit env : Map[Int,(Expr,Type)]) : Expr = { 
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
      case Some(BoolType) => semB(t) == semB(res)
      case Some(IntType) => semI(t) == semI(res)
    })
  }

} 
