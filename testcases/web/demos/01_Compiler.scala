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
  case class TInt(v: BigInt) extends Token
  case class TId(name: BigInt) extends Token // All variables are : BigInt
}

object Trees {
  abstract class Expr
  case class Times(lhs: Expr, rhs: Expr) extends Expr
  case class Plus(lhs: Expr, rhs: Expr) extends Expr
  case class And(lhs: Expr, rhs: Expr) extends Expr
  case class Or(lhs: Expr, rhs: Expr) extends Expr
  case class Var(id: BigInt) extends Expr
  case class IntLiteral(v: BigInt) extends Expr
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

object Simplifier {
  import Trees._ 
  import Runtime._
  
  //  Constant folding +  tautologies
  def simplify(e: Expr)(implicit m: Map[BigInt, BigInt]): Expr = (e match {
    // Special cases
    case Plus(IntLiteral(a), IntLiteral(b)) => IntLiteral(a+b)
    case LessThan(Var(id1), Var(id2)) if id1 == id2 => IntLiteral(0)
    
    // Recursion
    case Times(lhs, rhs) => Times(simplify(lhs), simplify(rhs))
    case Plus(lhs, rhs) => Plus(simplify(lhs), simplify(rhs))
    case And(lhs, rhs) => And(simplify(lhs), simplify(rhs))
    case Or(lhs, rhs) => And(simplify(lhs), simplify(rhs))
    case LessThan(lhs, rhs) => LessThan(simplify(lhs), simplify(rhs))
    case Ite(cond, thn, elze) => Ite(simplify(cond), simplify(thn), simplify(elze))
    case _ => e
  }) ensuring {
    res => run(res)(m) == run(e)(m)
  }

}

object Runtime {
  import Trees._
  
  def run(e: Expr)(implicit m: Map[BigInt, BigInt]): BigInt = e match {
    case Times(lhs, rhs) => run(lhs) * run(rhs)
    case Plus(lhs, rhs) => run(lhs) + run(rhs)
    case And(lhs, rhs) => run(lhs) * run(rhs)
    case Or(lhs, rhs) => if ((run(lhs) + run(rhs)) > 0) 1 else 0
    case IntLiteral(v) => v
    case Var(id) => if (m contains id) m(id) else 0
    case LessThan(lhs, rhs) => if (run(lhs) < run(rhs)) 1 else 0
    case Ite(cond, thn, elze) => if (run(cond) != 0) run(thn) else run(elze)
  }
  
  def test() = {
    run(Plus(IntLiteral(42), Var(0)))(Map(BigInt(0) -> BigInt(1))) 
  }
}



