package purescala

import z3.scala._
import Common._
import Extensions._
import Trees._
import TypeTrees._

class Z3Solver(reporter: Reporter) extends Solver(reporter) {
  val description = "Z3 Solver"
  override val shortDescription = "Z3"

  def solve(vc: Expr) : Option[Boolean] = {
    val z3cfg = new Z3Config()
    z3cfg.setParamValue("MODEL", "true")
    val z3 = new Z3Context(z3cfg)

    toZ3Formula(z3, vc) match {
      case None => None // means it could not be translated
      case Some(z3f) => {
        z3.assertCnstr(z3.mkNot(z3f))
        //z3.print
        z3.checkAndGetModel() match {
          case (Some(true),m) => {
            reporter.error("There's a bug! Here's a model for a counter-example:")
            m.print
            Some(false)
          }
          case (Some(false),_) => Some(true)
          case (None,_) => {
            reporter.error("Z3 couldn't run properly or does not know the answer :(")
            None
          }
        }
      }
    }
  }

  def toZ3Formula(z3: Z3Context, expr: Expr) : Option[Z3AST] = {
    class CantTranslateException extends Exception

    lazy val intSort  = z3.mkIntSort()
    lazy val boolSort = z3.mkBoolSort()

    // because we create identifiers the first time we see them, this is
    // convenient.
    var z3Vars: Map[Identifier,Z3AST] = Map.empty

    def rec(ex: Expr) : Z3AST = ex match {
      case Let(i,e,b) => {
        z3Vars = z3Vars + (i -> rec(e))
        rec(b)
      }
      case v @ Variable(id) => z3Vars.get(id) match {
        case Some(ast) => ast
        case None => {
          val newAST = if(v.getType == Int32Type) {
            z3.mkConst(z3.mkStringSymbol(id.name), intSort)
          } else if(v.getType == BooleanType) {
            z3.mkConst(z3.mkStringSymbol(id.name), boolSort)
          } else {
            reporter.warning("Unsupported type in Z3 transformation: " + v.getType)
            throw new CantTranslateException
          }
          z3Vars = z3Vars + (id -> newAST)
          newAST
        }
      } 
      case IfExpr(c,t,e) => z3.mkITE(rec(c), rec(t), rec(e))
      case And(exs) => z3.mkAnd(exs.map(rec(_)) : _*)
      case Or(exs) => z3.mkOr(exs.map(rec(_)) : _*)
      case Not(Equals(l,r)) => z3.mkDistinct(rec(l),rec(r))
      case Not(e) => z3.mkNot(rec(e))
      case Implies(l,r) => z3.mkImplies(rec(l), rec(r))
      case IntLiteral(v) => z3.mkInt(v, intSort)
      case BooleanLiteral(v) => if (v) z3.mkTrue() else z3.mkFalse()
      case Equals(l,r) => z3.mkEq(rec(l),rec(r))
      case Plus(l,r) => z3.mkAdd(rec(l), rec(r))
      case Minus(l,r) => z3.mkSub(rec(l), rec(r))
      case Times(l,r) => z3.mkMul(rec(l), rec(r))
      case Division(l,r) => z3.mkDiv(rec(l), rec(r))
      case UMinus(e) => z3.mkUnaryMinus(rec(e))
      case LessThan(l,r) => z3.mkLT(rec(l), rec(r)) 
      case LessEquals(l,r) => z3.mkLE(rec(l), rec(r)) 
      case GreaterThan(l,r) => z3.mkGT(rec(l), rec(r)) 
      case GreaterEquals(l,r) => z3.mkGE(rec(l), rec(r)) 
      case _ => {
        reporter.warning("Can't handle this in translation to Z3: " + ex)
        throw new CantTranslateException
      }
    }
    
    try {
      Some(rec(expr))
    } catch {
      case e: CantTranslateException => None
    }
  }
}
