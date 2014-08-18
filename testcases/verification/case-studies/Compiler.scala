import leon.lang._
import leon.annotation._
import leon.collection._
import leon._

object Tokens {
  abstract class Token
  case object TPlus extends Token
  case object TTimes extends Token
  case object TLT extends Token
  case object TIf extends Token
  case object TElse extends Token
  case object TLAnd extends Token
  case object TLOr extends Token
  case object TLeftBrace extends Token
  case object TRightBrace extends Token
  case object TLeftPar extends Token
  case object TRightPar extends Token
  case class TInt(v: Int) extends Token
  case class TId(name: Int) extends Token // All variables are : Int
}

object Trees {
  abstract class Expr
  case class Times(lhs: Expr, rhs: Expr) extends Expr
  case class Plus(lhs: Expr, rhs: Expr) extends Expr
  case class And(lhs: Expr, rhs: Expr) extends Expr
  case class Or(lhs: Expr, rhs: Expr) extends Expr
  case class Var(id: Int) extends Expr
  case class IntLiteral(v: Int) extends Expr
  case class LessThan(lhs: Expr, rhs: Expr) extends Expr
  case class Ite(cond: Expr, thn: Expr, els: Expr) extends Expr
}

object Types {
  abstract class Type
  case object IntType extends Type
  case object BoolType extends Type
}

object Parser {
  import Tokens._
  import Trees._

  def parsePhrase(ts: List[Token]): Option[Expr] = {
    parseGoal(ts) match {
      case Some((res, Nil())) => Some(res)
      case _ => None()
    }
  }

  def parseGoal(ts: List[Token]): Option[(Expr, List[Token])] = {
    parseOr(ts)
  }

  def parseOr(ts: List[Token]): Option[(Expr, List[Token])] = {
    parseAnd(ts) match {
      case Some((lhs, Cons(TLOr, r))) =>
        parseAnd(r) match {
          case Some((rhs, ts2)) => Some((Or(lhs, rhs), ts2))
          case None() => None()
        }
      case r => r
    }
  }

  def parseAnd(ts: List[Token]): Option[(Expr, List[Token])] = {
    parseLT(ts) match {
      case Some((lhs, Cons(TLAnd, r))) =>
        parseLT(r) match {
          case Some((rhs, ts2)) => Some((And(lhs, rhs), ts2))
          case None() => None()
        }
      case r => r
    }
  }

  def parseLT(ts: List[Token]): Option[(Expr, List[Token])] = {
    parsePlus(ts) match {
      case Some((lhs, Cons(TLT, r))) =>
        parsePlus(r) match {
          case Some((rhs, ts2)) => Some((LessThan(lhs, rhs), ts2))
          case None() => None()
        }
      case r => r
    }
  }

  def parsePlus(ts: List[Token]): Option[(Expr, List[Token])] = {
    parseTimes(ts) match {
      case Some((lhs, Cons(TPlus, r))) =>
        parsePlus(r) match {
          case Some((rhs, ts2)) => Some((Plus(lhs, rhs), ts2))
          case None() => None()
        }
      case r => r
    }
  }

  def parseTimes(ts: List[Token]): Option[(Expr, List[Token])] = {
    parseLits(ts) match {
      case Some((lhs, Cons(t, r))) if (t == TTimes) =>
        parseTimes(r) match {
          case Some((rhs, ts2)) => Some((Plus(lhs, rhs), ts2))
          case None() => None()
        }
      case r => r
    }
  }

  def parseLits(ts: List[Token]): Option[(Expr, List[Token])] = ts match {
    case Cons(TInt(v), r) => Some((IntLiteral(v), r))
    case Cons(TId(v), r) => Some((Var(v), r))
    case Cons(TLeftPar, r) =>
      parseGoal(r) match {
        case Some((e, Cons(TRightPar, ts2))) => Some((e, ts2))
        case _ => None()
      }
    case Cons(TIf, Cons(TLeftPar, r)) =>
      parseGoal(r) match {
        case Some((c, Cons(TRightPar, Cons(TLeftBrace, ts2)))) =>
          // Then
          parseGoal(ts2) match {
            case Some((th, Cons(TRightBrace, Cons(TElse, Cons(TLeftBrace, ts3))))) =>
              // Else
              parseGoal(ts3) match {
                case Some((el, Cons(TRightBrace, ts4))) =>
                  Some((Ite(c, th, el), ts4))
                case _ => None()
              }
            case _ => None()
          }
        case _ => None()
      }
    case _ => None()
  }
}

object TypeChecker {
  import Trees._
  import Types._

  def typeChecks(e: Expr, exp: Option[Type]): Boolean = e match {
    case Times(l, r)    => (exp.getOrElse(IntType) == IntType)   && typeChecks(l, Some(IntType))  && typeChecks(r, Some(IntType))
    case Plus(l, r)     => (exp.getOrElse(IntType) == IntType)   && typeChecks(l, Some(IntType))  && typeChecks(r, Some(IntType))
    case And(l, r)      => (exp.getOrElse(BoolType) == BoolType) && typeChecks(l, Some(BoolType)) && typeChecks(r, Some(BoolType))
    case Or(l, r)       => (exp.getOrElse(BoolType) == BoolType) && typeChecks(l, Some(BoolType)) && typeChecks(r, Some(BoolType))
    case LessThan(l, r) => (exp.getOrElse(BoolType) == BoolType) && typeChecks(l, Some(IntType))  && typeChecks(r, Some(IntType))
    case Ite(c, th, el) => typeChecks(c, Some(BoolType)) && typeChecks(th, exp) && typeChecks(el, exp)
    case IntLiteral(_)  => exp.getOrElse(IntType) == IntType
    case Var(_)         => exp.getOrElse(IntType) == IntType
  }

  def typeChecks(e: Expr): Boolean = typeChecks(e, None())
}

object Compiler {
  import Tokens._
  import Trees._
  import Types._
  import Parser._
  import TypeChecker._


  def parse(ts: List[Token]): Option[Expr] = {
    parsePhrase(ts)
  } ensuring { _ match {
    case Some(tree) => typeChecks(tree)
    case None()     => true
  }}
}
