import leon.lang._
import leon.annotation._
import leon.collection._
import leon.lang.synthesis._
import leon._

object Lang {
  case class Id(v: Int)

  def isLiteral(l: Expr) = l match {
    case _: Var => true
    case _: Abs => true
    //case _: Record => true
    case _ => false
  }

  abstract class Expr
  case class Var(id: Id) extends Expr
  case class App(f: Expr, arg: Expr) extends Expr
  case class Abs(b: Id, tpe: Type, e: Expr) extends Expr
  //case class Record(fields: Map[Id, Expr]) extends Expr
  //case class Select(r: Expr, f: Var) extends Expr

  abstract class Type
  case class Param(k : Int) extends Type
  case class TFunction(from: Type, to: Type) extends Type
  //case class TRecord(fields: Map[Id, Type]) extends Type
}



object TypeChecker {
  import Lang._

  def typeOf(e: Expr, exp: Option[Type], env: Map[Id, Type]): Option[Type] = {
    val t: Option[Type] = e match {
      case Var(id) =>
        if (env contains id) {
          Some(env(id))
        } else {
          None()
        }

      case App(f, arg) =>
        typeOf(f, None(), env) match {
          case Some(TFunction(from, to)) =>
            typeOf(arg, Some(from), env) match {
              case Some(_) => Some(to)
              case _ => None()
            }
          case _ => None()
        }
      case Abs(id, tpe, e) =>
        val nenv = env.updated(id, tpe)
        (exp, typeOf(e, None(), nenv)) match {
          case (Some(TFunction(from, to)), Some(to2)) if (from == tpe) && (to == to2) =>
            Some(TFunction(tpe, to2))
          case (None(), Some(to2)) =>
            Some(TFunction(tpe, to2))
          case _ =>
            None()
        }
    }

    if(exp.orElse(t) == t) {
      t
    } else {
      None()
    }
  }

  def typeChecks(e: Expr): Boolean = {
    typeOf(e, None(), Map[Id, Type]()).isDefined
  }

  def typeOf(e: Expr): Option[Type] = {
    typeOf(e, None(), Map[Id, Type]())
  }
}

object Evaluator {
  import Lang._
  import TypeChecker._

  def subst(e: Expr, t: (Id, Expr)): Expr = e match {
    case Var(id) if id == t._1 => t._2
    case App(f, arg) => App(subst(f, t), subst(arg, t))
    case Abs(b, id, e) => Abs(b, id, subst(e, t))
    case _ => e
  }

  def eval(e: Expr): Expr = {
    require(typeChecks(e))
    e match {
    case App(f, arg) =>
      eval(f) match {
        case Abs(id, _, e) => eval(subst(e, id -> arg))
        case _ => e // stuck
      }
    case _ =>
      e
  }} ensuring { res => isLiteral(res) }
}

object Main {
  import Lang._
  import Evaluator._
  import TypeChecker._

  def synthesize_identity() : Expr = {
    choose { (e : Expr) =>
      val t_identity : Type = TFunction(Param(1), Param(1))
      typeOf(e) == Some(t_identity)
    }
  }

  def synthesize_K() : Expr = {
    choose { (e : Expr) =>
      val t1 : Type = TFunction(Param(1), TFunction(Param(2), Param(1)))
      typeOf(e) == Some(t1)
    }
  }
  def synthesize_K2() : Expr = {
    choose { (e : Expr) =>
      val t1 : Type = TFunction(Param(1), TFunction(Param(2), Param(2)))
      typeOf(e) == Some(t1)
    }
  }


  def synthesize_S() : Expr = {
    choose { (e : Expr) =>
      val tz = Param(1)
      val ty = TFunction(Param(1), Param(2))
      val tx = TFunction(Param(1), TFunction(Param(2), Param(3)))
      val t1 : Type = TFunction(tx,
                        TFunction(ty, 
                          TFunction(tz, Param(3))))
      typeOf(e) == Some(t1)
    }
  }
}
