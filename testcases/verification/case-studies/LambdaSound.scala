import leon.lang._
import leon.annotation._
import leon.collection._
import leon.lang.synthesis._
import leon._

object Lambda {
  case class Id(v: BigInt)

  abstract class Expr
  case class Var(id: Id) extends Expr
  case class App(f: Expr, arg: Expr) extends Expr
  case class Abs(b: Id, tpe: Type, e: Expr) extends Expr
  
  case class Env(binds: Map[Id, Expr])

  abstract class Type
  case object Tind extends Type
  case object Tbool extends Type
  case class Arrow(from: Type, to: Type) extends Type

  case class TEnv(binds: Map[Id, Type])

  def fv(e: Expr): Set[Id] = e match {
    case Var(id) => Set(id)
    case App(f, arg) => fv(f) ++ fv(arg)
    case Abs(b, _, e) => fv(e) -- Set(b)
  }
  
  def subst(in: Expr, v: Id, by: Expr): Expr = {
    in match {
      case Var(id) => {
        if (id==v) by
        else in
      }
      case App(f, arg) => App(subst(f, v, by), subst(arg, v, by))
      case Abs(b, tpe, e) => {
        if (b==v) in
        else { // ADD CHECK FOR CAPTURE HERE
          Abs(b, tpe, subst(e, v, by))
        }
      }
    }
  }
  
  def id1 = Id(BigInt(1))
  def id2 = Id(BigInt(2))
  def exprId = Abs(id1, Tind, Var(id1))

  abstract class Outcome
  case class Ok(v: Expr) extends Outcome
  case class Err(s: String, sub: Expr) extends Outcome

  def CBV(env: Env, e: Expr): Outcome = {
    e match {
      case Var(id) => { env.binds.get(id) match {
        case None() => Err("Unknown identifier in environment", e)
        case Some(expr) => Ok(expr)
      }}
      case Abs(b, tpe, body) => Ok(e)
      case App(f, arg) => { CBV(env, f) match {
        case Ok(Abs(b, t, fbody)) => { CBV(env, arg) match {
          case Ok(argv) => CBV(env, subst(fbody, b, argv))
          case err => err
        }}
        case Ok(expr) => Err("Tried to apply non-function value", expr)
        case err => err
      }}
    }
  }
  
  def env1 : Env = Env(Map[Id,Expr](id2 -> Var(id2)))
  def r1 = CBV(env1, App(exprId, Var(id2)))

  def substOk(in: Expr, v: Id, by: Expr, env: Env): Boolean = {
    val vRes= CBV(env, Var(v))
    val byRes= CBV(env, by)
    val inRes= CBV(env, in)
    if (vRes==byRes && vRes.isInstanceOf[Ok] && inRes.isInstanceOf[Ok]) {
      inRes==CBV(env, subst(in, v, by))
    } else true
  }.holds

}

