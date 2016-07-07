
package leon
package verification

import purescala.Common._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Definitions._
import purescala.Constructors._
import purescala.Types._
import theorem.Library

class TermConverter(vctx: VerificationContext) {

  val library = Library(vctx.program)
  
  def fromPureScala(expr: Expr, env: Identifier => String): Expr = expr match {
    case Variable(identifier) => caseClass(library.Variable, StringLiteral(env(identifier)))
    case v@IntLiteral(_) => caseClass(library.IntLiteral, v)
    case v@InfiniteIntegerLiteral(_) => caseClass(library.BigIntLiteral, v)
    case v@StringLiteral(_) => caseClass(library.StringLiteral, v)
    case v@BooleanLiteral(_) => caseClass(library.BooleanLiteral, v)
    case Equals(left, right) => caseClass(library.Equals,
      fromPureScala(left, env),
      fromPureScala(right, env))
    case And(exprs) => fold(library.And, exprs)
    case Or(exprs) => fold(library.Or, exprs)
    case Implies(left, right) => caseClass(library.Implies,
      fromPureScala(left, env),
      fromPureScala(right, env)) 
    case _ => throw new Exception("Unsupported expression.")
  }

  def caseClass(cc: Option[CaseClassDef], args: Expr*) =
    CaseClass(CaseClassType(cc.get, Seq()), args.toSeq)

  def fold(cc: Option[CaseClassDef], args: Seq[Expr]): Expr = {
    require(args.size >= 2)

    if (args.size == 2) {
      caseClass(cc, args : _*)
    }
    else {
      caseClass(cc, args.head, fold(cc, args.tail))
    }
  }

  def toPureScala(expr: Expr): Expr = expr match {
    case _ => throw new Exception("Unsupported expression.")
  }
}