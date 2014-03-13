import leon.lang._
import leon.annotation._
import leon.collection._
import leon._

object Lang {
  case class Id(v: Int)

  def isLiteral(l: Expr) = l match {
    case _: Var => true
    case _: Abs => true
    case _: BoolLit => true
    case _: IntLit => true
    //case _: Record => true
    case _ => false
  }

  abstract class Expr
  case class Var(id: Id) extends Expr
  case class IntLit(v: Int) extends Expr
  case class BoolLit(v: Boolean) extends Expr
  case class App(f: Expr, arg: Expr) extends Expr
  case class Abs(b: Id, tpe: Type, e: Expr) extends Expr
  //case class Record(fields: Map[Id, Expr]) extends Expr
  //case class Select(r: Expr, f: Var) extends Expr

  abstract class Type
  case object TBool extends Type
  case object TInt extends Type
  case class  TApp(from: Type, to: Type) extends Type
  //case class  TRecord(fields: Map[Id, Type]) extends Type
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

      case _: IntLit =>
        Some(TInt)

      case _: BoolLit =>
        Some(TBool)

      case App(f, arg) =>
        typeOf(f, None(), env) match {
          case Some(TApp(from, to)) =>
            typeOf(arg, Some(from), env) match {
              case Some(_) => Some(to)
              case _ => None()
            }
          case _ => None()
        }
      case Abs(id, tpe, e) =>
        val nenv = env.updated(id, tpe)
        (exp, typeOf(e, None(), nenv)) match {
          case (Some(TApp(from, to)), Some(to2)) if (from == tpe) && (to == to2) =>
            Some(TApp(tpe, to2))
          case (None(), Some(to2)) =>
            Some(TApp(tpe, to2))
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

  def test() : Expr = {
    val x = Var(Id(0))
    val y = Var(Id(1))

    eval(App(Abs(Id(0), TInt, x), IntLit(42)))
  }
}
